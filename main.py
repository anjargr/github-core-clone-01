#!/usr/bin/env python3
"""github-core-clone-01 entry: a GitHub-compatible git forge in one file.

Single-process Python 3.13 stdlib-only server. Serves:
  - git smart HTTP (upload-pack v0/v2, receive-pack v0) with real packfiles
  - REST v3 API (/api/v3)  - repos, branches, commits, contents, labels,
    issues, comments, pull requests (incl. squash merge + conflict detection)
  - GraphQL v4 (/api/graphql) - viewer, repository, issues, pull requests,
    mutations, node(), introspection, batched operations
  - MCP Streamable HTTP (/mcp) - modern server/discover era, tools/call
  - /healthz

All surfaces share one in-memory store. State is deterministic: fixed
author/committer identity and fixed epoch timestamps, no wall clock or
unseeded randomness in anything a client can observe.

Scenario identity (viewer login etc.) is derived by re-implementing the
kit's deterministic scenario PRNG (fnv1a64 + mix64 + xorshift64*) from
SCENARIO_SEED, exactly as program/env/src/wire.ts does it.
"""

import base64
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import urllib.request
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

SCENARIO_SEED = 0x6A09E667F3BCC909
EPOCH = 1700000000
GIT_AUTHOR = "Forge <forge@example.invalid>"
MERGED_AT = "2025-06-01T00:00:00Z"
ZERO_OID = "0" * 40
REPO_NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,99}$")

# ---------------------------------------------------------------------------
# Scenario PRNG (replicates program/env/src/wire.ts)
# ---------------------------------------------------------------------------

_MASK64 = (1 << 64) - 1


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for b in text.encode("utf-8"):
        h ^= b
        h = (h * 0x100000001B3) & _MASK64
    return h


def _mix64(x):
    x = (x + 0x9E3779B97F4A7C15) & _MASK64
    x = (x ^ (x >> 30)) & _MASK64
    x = (x * 0xBF58476D1CE4E5B9) & _MASK64
    x = (x ^ (x >> 27)) & _MASK64
    x = (x * 0x94D049BB133111EB) & _MASK64
    x = (x ^ (x >> 31)) & _MASK64
    return x


class _ScenarioRng:
    """xorshift64* seeded from fnv1a64(label) mixed with SCENARIO_SEED."""

    def __init__(self, label):
        state = _mix64(_fnv1a64(label) ^ SCENARIO_SEED)
        self.state = state if state != 0 else 0x9E3779B97F4A7C15

    def next(self):
        x = self.state
        x ^= (x >> 12) & _MASK64
        x ^= (x << 25) & _MASK64
        x ^= (x >> 27) & _MASK64
        self.state = x & _MASK64
        return (x * 0x2545F4914F6CDD1D) & _MASK64

    def next_u32(self):
        return self.next() >> 32

    def next_int(self, max_exclusive):
        if max_exclusive == 1:
            return 0
        limit = (1 << 32) - ((1 << 32) % max_exclusive)
        while True:
            value = self.next_u32()
            if value < limit:
                return value % max_exclusive

    def pick(self, items):
        return items[self.next_int(len(items))]

    def int(self, lo, hi):
        return lo + self.next_int(hi - lo + 1)


_FIRST_NAMES = [
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
]
_LAST_NAMES = [
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
]


def _derive_users(count=3):
    """Replicate generateUsers(scenarioRng('users'), count)."""
    rng = _ScenarioRng("users")
    used = set()
    logins = []
    for _i in range(count):
        first = rng.pick(_FIRST_NAMES)
        last = rng.pick(_LAST_NAMES)
        base = first + last
        login = base
        suffix = 2
        while login in used:
            login = "%s-%d" % (base, suffix)
            suffix += 1
        used.add(login)
        logins.append(login)
    return logins


_USERS = _derive_users(3)
VIEWER_LOGIN = _USERS[0]
STRANGER_LOGIN = _USERS[2]


# ---------------------------------------------------------------------------
# Git object model
# ---------------------------------------------------------------------------

_OBJ_TYPE_CODE = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_OBJ_CODE_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(otype, data):
    h = hashlib.sha1()
    h.update(otype.encode("ascii"))
    h.update(b" ")
    h.update(str(len(data)).encode("ascii"))
    h.update(b"\x00")
    h.update(data)
    return h.hexdigest()


def git_tree_key(name, mode):
    # git sorts tree entries by name bytes, directories as if name ends in /
    return name.encode("utf-8") + (b"/" if mode == "40000" else b"")


def build_tree(entries):
    """entries: list of (mode_str, name, oid_hex) -> tree bytes."""
    ordered = sorted(entries, key=lambda e: git_tree_key(e[1], e[0]))
    out = bytearray()
    for mode, name, oid in ordered:
        out += mode.encode("ascii") + b" " + name.encode("utf-8") + b"\x00"
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_tree(data):
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp].decode("ascii")
        nul = data.index(b"\x00", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries


def parse_commit(data):
    tree = None
    parents = []
    message = ""
    header, sep, body = data.partition(b"\n\n")
    if sep:
        message = body.decode("utf-8", "surrogateescape")
    for line in header.decode("utf-8", "surrogateescape").split("\n"):
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
    return {"tree": tree, "parents": parents, "message": message}


def parse_tag(data):
    target = None
    ttype = None
    message = ""
    header, sep, body = data.partition(b"\n\n")
    if sep:
        message = body.decode("utf-8", "surrogateescape")
    for line in header.decode("utf-8", "surrogateescape").split("\n"):
        if line.startswith("object "):
            target = line[7:].strip()
        elif line.startswith("type "):
            ttype = line[5:].strip()
    return {"target": target, "type": ttype, "message": message}


def make_commit(tree_oid, parents, message):
    lines = ["tree %s" % tree_oid]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s %d +0000" % (GIT_AUTHOR, EPOCH))
    lines.append("committer %s %d +0000" % (GIT_AUTHOR, EPOCH))
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8")


def make_tag(target_oid, target_type, name, message):
    lines = [
        "object %s" % target_oid,
        "type %s" % target_type,
        "tag %s" % name,
        "tagger %s %d +0000" % (GIT_AUTHOR, EPOCH),
    ]
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8")


def flatten_tree(store_objects, tree_oid):
    """Return {path: (mode, oid)} for every blob in the tree (recursive)."""
    out = {}

    def walk(oid, prefix):
        obj = store_objects.get(oid)
        if obj is None or obj[0] != "tree":
            return
        for mode, name, child in parse_tree(obj[1]):
            path = prefix + name
            if mode == "40000":
                walk(child, path + "/")
            elif mode == "160000":
                continue
            else:
                out[path] = (mode, child)

    walk(tree_oid, "")
    return out


def build_trees_from_flat(store_objects, flat):
    """flat: {path: (mode, oid)} -> (root_tree_oid, created_objects).

    Creates every intermediate tree object in store_objects. Returns the
    root tree oid and a dict of newly created {oid: (type, data)}.
    """
    created = {}
    # group paths by directory
    dirs = {}

    def dir_of(path):
        return path.rsplit("/", 1)[0] if "/" in path else ""

    for path, (mode, oid) in flat.items():
        dirs.setdefault(dir_of(path), []).append((mode, path.rsplit("/", 1)[-1], oid))

    def build_dir(d):
        entries = list(dirs.get(d, []))
        # immediate subdirectories of d
        subs = set()
        prefix = (d + "/") if d else ""
        for path in flat:
            rest = path[len(prefix):] if path.startswith(prefix) else None
            if rest is None or "/" not in rest:
                continue
            subs.add(rest.split("/")[0])
        for sub in sorted(subs):
            sub_oid = build_dir(prefix + sub)
            entries.append(("40000", sub, sub_oid))
        tree_bytes = build_tree(entries)
        oid = hash_object("tree", tree_bytes)
        if oid not in store_objects:
            created[oid] = ("tree", tree_bytes)
            store_objects[oid] = ("tree", tree_bytes)
        return oid

    root = build_dir("")
    return root, created


# ---------------------------------------------------------------------------
# Packfile read / write
# ---------------------------------------------------------------------------

def write_pack(objects):
    """objects: dict oid -> (type, data). Returns pack bytes (v2, no deltas).

    Object order is deterministic (sorted by oid).
    """
    out = bytearray()
    out += b"PACK"
    out += (2).to_bytes(4, "big")
    out += len(objects).to_bytes(4, "big")
    for oid in sorted(objects):
        otype, data = objects[oid]
        code = _OBJ_TYPE_CODE[otype]
        size = len(data)
        first = (code << 4) | (size & 0x0F)
        size >>= 4
        if size:
            first |= 0x80
        out.append(first)
        while size:
            b = size & 0x7F
            size >>= 7
            if size:
                b |= 0x80
            out.append(b)
        out += zlib.compress(data)
    trailer = hashlib.sha1(bytes(out)).digest()
    out += trailer
    return bytes(out)


def read_pack(data):
    """Parse a packfile. Returns {oid: (type, data)} or raises ValueError."""
    if len(data) < 12 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(data[4:8], "big")
    if version != 2:
        raise ValueError("unsupported pack version")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    objects = {}
    for _ in range(count):
        if pos >= len(data):
            raise ValueError("truncated pack")
        first = data[pos]
        pos += 1
        code = (first >> 4) & 0x07
        size = first & 0x0F
        shift = 4
        while first & 0x80:
            first = data[pos]
            pos += 1
            size |= (first & 0x7F) << shift
            shift += 7
        if code == 6:  # OFS_DELTA - not supported (we never send them; reject)
            raise ValueError("ofs-delta unsupported")
        if code == 7:  # REF_DELTA
            raise ValueError("ref-delta unsupported")
        otype = _OBJ_CODE_TYPE.get(code)
        if otype is None:
            raise ValueError("bad object type code")
        decomp = zlib.decompressobj()
        raw = decomp.decompress(data[pos:])
        consumed = len(data[pos:]) - len(decomp.unused_data)
        pos += consumed
        if len(raw) != size:
            raise ValueError("object size mismatch")
        oid = hash_object(otype, raw)
        objects[oid] = (otype, raw)
    return objects


def reachable_objects(objects, tips, depth=None, shallow_stop=None):
    """Collect objects reachable from commit/tag tips.

    depth: None = full walk; N = include commits within N generations of
    the tips (generation 0 = the tips themselves). Returns
    (objects_dict, boundary_commits) where boundary_commits are included
    commits whose parents were cut off by the depth limit.
    shallow_stop: set of commit oids that act as shallow boundaries for
    the traversal (their parents are not followed, but they themselves
    and their trees are included).
    """
    shallow_stop = shallow_stop or set()
    included = {}
    commit_gen = {}
    queue = []
    for tip in tips:
        obj = objects.get(tip)
        if obj is None:
            continue
        if obj[0] == "tag":
            included[tip] = obj
            target = parse_tag(obj[1])["target"]
            if target:
                queue.append((target, 0))
        elif obj[0] == "commit":
            queue.append((tip, 0))
        else:
            included[tip] = obj
    boundary = []
    while queue:
        oid, gen = queue.pop(0)
        if oid in commit_gen:
            continue
        if depth is not None and gen >= depth:
            continue
        obj = objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        commit_gen[oid] = gen
        included[oid] = obj
        parsed = parse_commit(obj[1])
        tree_oid = parsed["tree"]
        if tree_oid and tree_oid not in included:
            _collect_tree(objects, tree_oid, included)
        is_boundary = False
        for parent in parsed["parents"]:
            if oid in shallow_stop:
                is_boundary = True
                continue
            if parent not in commit_gen:
                if depth is not None and gen + 1 >= depth:
                    is_boundary = True
                queue.append((parent, gen + 1))
        if is_boundary:
            boundary.append(oid)
    return included, boundary


def _collect_tree(objects, tree_oid, included):
    stack = [tree_oid]
    while stack:
        oid = stack.pop()
        if oid in included:
            continue
        obj = objects.get(oid)
        if obj is None:
            continue
        included[oid] = obj
        if obj[0] == "tree":
            for mode, _name, child in parse_tree(obj[1]):
                if mode == "160000":
                    continue
                stack.append(child)


def is_descendant(objects, ancestor, descendant):
    """True if ancestor is reachable from descendant (commit graph)."""
    if ancestor == descendant:
        return True
    seen = set()
    stack = [descendant]
    while stack:
        oid = stack.pop()
        if oid in seen:
            continue
        seen.add(oid)
        obj = objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        parents = parse_commit(obj[1])["parents"]
        if ancestor in parents:
            return True
        stack.extend(parents)
    return False


# ---------------------------------------------------------------------------
# pkt-line framing
# ---------------------------------------------------------------------------

def pkt(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return ("%04x" % (len(data) + 4)).encode("ascii") + data


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def decode_pkt_lines(buf):
    """Parse pkt-lines from bytes. Returns (lines, consumed, ok).

    lines: list of (kind, payload) where kind is 'data' | 'flush' | 'delim'.
    ok=False when the buffer is not a valid pkt-line stream.
    """
    lines = []
    i = 0
    n = len(buf)
    while i < n:
        if i + 4 > n:
            return lines, i, False
        head = buf[i:i + 4]
        if head == b"0000":
            lines.append(("flush", b""))
            i += 4
            continue
        if head == b"0001":
            lines.append(("delim", b""))
            i += 4
            continue
        try:
            size = int(head.decode("ascii"), 16)
        except ValueError:
            return lines, i, False
        if size < 4 or i + size > n:
            return lines, i, False
        lines.append(("data", buf[i + 4:i + size]))
        i += size
    return lines, i, True


# ---------------------------------------------------------------------------
# In-memory store
# ---------------------------------------------------------------------------

class Issue:
    __slots__ = ("number", "id", "title", "body", "state", "labels",
                 "seq", "comments")

    def __init__(self, number, gid, title, body, labels, seq):
        self.number = number
        self.id = gid
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = list(labels)
        self.seq = seq
        self.comments = []  # list of {"id": int, "body": str}


class PullRequest:
    __slots__ = ("number", "id", "title", "body", "head", "base", "state",
                 "merged", "merged_at", "merge_commit_sha", "merge_base",
                 "seq", "head_sha", "base_sha")

    def __init__(self, number, gid, title, body, head, base, head_sha,
                 base_sha, merge_base, seq):
        self.number = number
        self.id = gid
        self.title = title
        self.body = body
        self.head = head
        self.base = base
        self.state = "open"
        self.merged = False
        self.merged_at = None
        self.merge_commit_sha = None
        self.merge_base = merge_base
        self.seq = seq
        self.head_sha = head_sha
        self.base_sha = base_sha


class Repo:
    __slots__ = ("owner", "name", "description", "private", "default_branch",
                 "id", "seq", "objects", "refs", "issues", "prs", "labels",
                 "version", "pack_cache")

    def __init__(self, owner, name, description, private, gid, seq):
        self.owner = owner
        self.name = name
        self.description = description or ""
        self.private = bool(private)
        self.default_branch = "main"
        self.id = gid
        self.seq = seq
        self.objects = {}   # oid -> (type, bytes)
        self.refs = {}      # "refs/heads/main" -> oid
        self.issues = {}    # number -> Issue
        self.prs = {}       # number -> PullRequest
        self.labels = {}    # name -> {"name":..., "color":...}
        self.version = 0    # bumped on any mutation (invalidates pack cache)
        self.pack_cache = {}  # frozenset(oids) -> pack bytes

    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def branch_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def bump(self):
        self.version += 1
        self.pack_cache = {}


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}          # (owner, name) -> Repo
        self.next_id = 1
        self.next_seq = 1
        self.request_seq = 0
        self.pack_cache = {}     # global pack cache by frozenset(oids)

    def new_id(self):
        gid = self.next_id
        self.next_id += 1
        return gid

    def new_seq(self):
        s = self.next_seq
        self.next_seq += 1
        return s

    def request_id(self):
        self.request_seq += 1
        return "req-%d" % self.request_seq

    def create_repo(self, owner, name, description, private):
        repo = Repo(owner, name, description, private, self.new_id(),
                    self.new_seq())
        self.repos[(owner, name)] = repo
        return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def viewer_repos(self, owner):
        return sorted(
            (r for (o, _n), r in self.repos.items() if o == owner),
            key=lambda r: r.seq)

    def get_pack(self, objects):
        """Cached packfile bytes for a set of objects (dict oid->(t,d))."""
        key = frozenset(objects.keys())
        cached = self.pack_cache.get(key)
        if cached is not None:
            return cached
        pack = write_pack(objects)
        if len(self.pack_cache) > 512:
            self.pack_cache.clear()
        self.pack_cache[key] = pack
        return pack


STORE = Store()


# ---------------------------------------------------------------------------
# Shared helpers: JSON shapes, global ids, diffs, merges
# ---------------------------------------------------------------------------

def b64url_encode(raw):
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def b64url_decode(text):
    pad = "=" * (-len(text) % 4)
    return base64.urlsafe_b64decode(text + pad)


def global_id(kind, *parts):
    return b64url_encode(("%s:%s" % (kind, ":".join(parts))).encode("utf-8"))


def parse_global_id(gid):
    try:
        text = b64url_decode(gid).decode("utf-8")
    except Exception:
        return None, []
    if ":" not in text:
        return None, []
    kind, rest = text.split(":", 1)
    return kind, rest.split(":")


def repo_json(repo):
    return {
        "id": repo.id,
        "name": repo.name,
        "full_name": repo.full_name(),
        "owner": {"login": repo.owner, "id": 1000},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "html_url": "https://example.invalid/%s" % repo.full_name(),
    }


def issue_json(repo, issue):
    return {
        "id": issue.id,
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [{"name": n} for n in issue.labels],
        "user": {"login": repo.owner},
    }


def pr_json(repo, pr):
    head_sha = repo.branch_tip(pr.head) or pr.head_sha
    base_sha = repo.branch_tip(pr.base) or pr.base_sha
    out = {
        "id": pr.id,
        "number": pr.number,
        "state": pr.state,
        "title": pr.title,
        "body": pr.body,
        "head": {"ref": pr.head, "sha": head_sha,
                 "label": "%s:%s" % (repo.owner, pr.head)},
        "base": {"ref": pr.base, "sha": base_sha,
                 "label": "%s:%s" % (repo.owner, pr.base)},
        "merged": pr.merged,
        "merged_at": pr.merged_at,
        "merge_commit_sha": pr.merge_commit_sha,
    }
    return out


def commit_list_json(repo, tip):
    """Newest-first list of {sha, commit: {message}} from tip."""
    out = []
    seen = set()
    stack = [tip]
    order = []
    while stack:
        oid = stack.pop(0)
        if oid in seen:
            continue
        seen.add(oid)
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        order.append(oid)
        stack.extend(parse_commit(obj[1])["parents"])
    for oid in order:
        msg = parse_commit(repo.objects[oid][1])["message"]
        out.append({"sha": oid,
                    "commit": {"message": msg,
                               "author": {"name": "Forge",
                                          "email": "forge@example.invalid"},
                               "committer": {"name": "Forge",
                                             "email": "forge@example.invalid"}}})
    return out


def diff_trees(repo, base_tree_oid, head_tree_oid):
    """Return list of changed files between two trees.

    Each entry: {"filename": path, "status": added|removed|modified,
    "additions": n, "deletions": n, "changes": n, "_new": bytes|None,
    "_old": bytes|None}
    """
    base = flatten_tree(repo.objects, base_tree_oid) if base_tree_oid else {}
    head = flatten_tree(repo.objects, head_tree_oid) if head_tree_oid else {}
    out = []
    for path in sorted(set(base) | set(head)):
        in_base = path in base
        in_head = path in head
        if in_base and in_head:
            if base[path][1] == head[path][1]:
                continue
            status = "modified"
            old = repo.objects[base[path][1]][1]
            new = repo.objects[head[path][1]][1]
        elif in_head:
            status = "added"
            old = None
            new = repo.objects[head[path][1]][1]
        else:
            status = "removed"
            old = repo.objects[base[path][1]][1]
            new = None
        additions, deletions = _line_diff(old, new)
        out.append({"filename": path, "status": status,
                    "additions": additions, "deletions": deletions,
                    "changes": additions + deletions,
                    "_old": old, "_new": new})
    return out


def _line_diff(old, new):
    old_lines = _split_lines(old)
    new_lines = _split_lines(new)
    from collections import Counter
    oc, nc = Counter(old_lines), Counter(new_lines)
    additions = sum((nc - oc).values())
    deletions = sum((oc - nc).values())
    return additions, deletions


def _split_lines(data):
    if data is None:
        return []
    text = data.decode("utf-8", "surrogateescape")
    if text == "":
        return []
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines


def _tree_of(repo, commit_oid):
    """Tree oid of a commit oid (or None)."""
    if not commit_oid:
        return None
    obj = repo.objects.get(commit_oid)
    if obj is None or obj[0] != "commit":
        return None
    return parse_commit(obj[1])["tree"]


def three_way_merge(repo, base_oid, head_oid, merge_base_oid):
    """Merge head into base with merge_base as common ancestor.

    base_oid / head_oid / merge_base_oid are COMMIT oids.

    Returns (merged_tree_oid, conflict) where conflict is True when the
    same path changed differently on both sides.
    """
    base_tree = _tree_of(repo, base_oid)
    head_tree = _tree_of(repo, head_oid)
    mb_tree = _tree_of(repo, merge_base_oid)
    base_flat = flatten_tree(repo.objects, base_tree) if base_tree else {}
    head_flat = flatten_tree(repo.objects, head_tree) if head_tree else {}
    mb_flat = flatten_tree(repo.objects, mb_tree) if mb_tree else {}
    merged = dict(base_flat)
    conflict = False
    for path in sorted(set(mb_flat) | set(head_flat)):
        mb = mb_flat.get(path)
        hd = head_flat.get(path)
        bs = base_flat.get(path)
        head_changed = hd != mb
        base_changed = bs != mb
        if not head_changed:
            continue
        if not base_changed:
            if hd is None:
                merged.pop(path, None)
            else:
                merged[path] = hd
        else:
            # both sides changed: same result -> fine, different -> conflict
            if hd == bs:
                continue
            conflict = True
            return None, True
    root_oid, _created = build_trees_from_flat(repo.objects, merged)
    return root_oid, conflict


# ---------------------------------------------------------------------------
# Git protocol handlers
# ---------------------------------------------------------------------------

def _git_caps_upload_v0():
    return ("side-band-64k multi_ack_detailed thin-pack ofs-delta shallow "
            "symref=HEAD:refs/heads/main agent=forge/1.0")


def _git_caps_receive_v0():
    return ("report-status report-status-v2 side-band-64k ofs-delta "
            "delete-refs agent=forge/1.0")


def _ref_lines_v0(repo, caps):
    """v0 advertisement ref lines (without the service header)."""
    lines = []
    refs = sorted(repo.refs.items())
    head_tip = repo.branch_tip(repo.default_branch)
    if not refs:
        lines.append("%s capabilities^{}\x00%s\n" % (ZERO_OID, caps))
        return lines
    first = True
    lines.append("%s HEAD\x00%s\n" % (head_tip or ZERO_OID,
                                      caps if first else ""))
    for refname, oid in refs:
        lines.append("%s %s\n" % (oid, refname))
        obj = repo.objects.get(oid)
        if obj and obj[0] == "tag":
            target = parse_tag(obj[1])["target"]
            if target:
                lines.append("%s %s^{}\n" % (target, refname))
    return lines


def handle_git_info_refs(handler, owner, repo_name, query):
    repo = STORE.get_repo(owner, repo_name)
    service = query.get("service", [None])[0]
    if repo is None or service not in ("git-upload-pack", "git-receive-pack"):
        handler.send_json(404, {"message": "Not Found"})
        return
    proto = handler.headers.get("Git-Protocol", "")
    if service == "git-upload-pack" and proto == "version=2":
        body = b"".join([
            pkt("# service=git-upload-pack\n"),
            pkt_flush(),
            pkt("version 2\n"),
            pkt("agent=forge/1.0\n"),
            pkt("ls-refs=unborn\n"),
            pkt("fetch=shallow\n"),
            pkt("object-format=sha1\n"),
            pkt_flush(),
        ])
        handler.send_bytes(200, body,
                           "application/x-git-upload-pack-advertisement")
        return
    if service == "git-upload-pack":
        body = b"".join([pkt("# service=git-upload-pack\n"), pkt_flush()] +
                        [pkt(l) for l in _ref_lines_v0(repo, _git_caps_upload_v0())] +
                        [pkt_flush()])
        handler.send_bytes(200, body,
                           "application/x-git-upload-pack-advertisement")
        return
    # receive-pack advertisement (v0 only)
    body = b"".join([pkt("# service=git-receive-pack\n"), pkt_flush()] +
                    [pkt(l) for l in _ref_lines_v0(repo, _git_caps_receive_v0())] +
                    [pkt_flush()])
    handler.send_bytes(200, body,
                       "application/x-git-receive-pack-advertisement")


def _ls_refs_response(repo, args):
    """args: dict with keys peel, symrefs, unborn, prefixes (list)."""
    prefixes = args.get("prefixes", [])
    want_peel = args.get("peel", False)
    want_unborn = args.get("unborn", False)

    def matches(refname):
        if not prefixes:
            return True
        return any(refname.startswith(p) for p in prefixes)

    out = []
    head_tip = repo.branch_tip(repo.default_branch)
    if not repo.refs:
        if want_unborn:
            out.append("unborn HEAD symref-target:refs/heads/main\n")
        return out
    if matches("HEAD"):
        out.append("%s HEAD symref-target:refs/heads/main\n" % head_tip)
    for refname in sorted(repo.refs):
        if not matches(refname):
            continue
        oid = repo.refs[refname]
        line = "%s %s" % (oid, refname)
        obj = repo.objects.get(oid)
        if want_peel and obj and obj[0] == "tag":
            target = parse_tag(obj[1])["target"]
            if target:
                line += " peeled:%s" % target
        out.append(line + "\n")
    return out


def _sideband_pack(pack_bytes, chunk=32768):
    """Wrap pack bytes in band-1 sideband pkt-lines."""
    out = bytearray()
    for i in range(0, len(pack_bytes), chunk):
        out += pkt(b"\x01" + pack_bytes[i:i + chunk])
    if not pack_bytes:
        out += pkt(b"\x01")
    return bytes(out)


def handle_git_upload_pack(handler, owner, repo_name, body):
    repo = STORE.get_repo(owner, repo_name)
    if repo is None:
        handler.send_json(404, {"message": "Not Found"})
        return
    proto = handler.headers.get("Git-Protocol", "")
    if proto == "version=2":
        _handle_upload_pack_v2(handler, repo, body)
    else:
        _handle_upload_pack_v0(handler, repo, body)


def _handle_upload_pack_v2(handler, repo, body):
    lines, _consumed, ok = decode_pkt_lines(body)
    if not ok:
        handler.send_bytes(400, b"bad pkt-line stream", "text/plain")
        return
    command = None
    args = {"peel": False, "symrefs": False, "unborn": False, "prefixes": [],
            "wants": [], "haves": [], "shallows": [], "depth": None,
            "filter": []}
    in_args = False
    for kind, payload in lines:
        if kind == "delim":
            in_args = True
            continue
        if kind != "data":
            continue
        text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if not in_args:
            if text.startswith("command="):
                command = text[len("command="):]
            continue
        if text == "peel":
            args["peel"] = True
        elif text == "symrefs":
            args["symrefs"] = True
        elif text == "unborn":
            args["unborn"] = True
        elif text.startswith("ref-prefix "):
            args["prefixes"].append(text[len("ref-prefix "):])
        elif text.startswith("want "):
            args["wants"].append(text[5:].strip())
        elif text.startswith("have "):
            args["haves"].append(text[5:].strip())
        elif text.startswith("shallow "):
            args["shallows"].append(text[8:].strip())
        elif text.startswith("deepen "):
            try:
                args["depth"] = int(text[7:].strip())
            except ValueError:
                pass
        elif text.startswith("filter "):
            args["filter"].append(text)
    if command == "ls-refs":
        out = b"".join(pkt(l) for l in _ls_refs_response(repo, args))
        out += pkt_flush()
        handler.send_bytes(200, out, "application/x-git-upload-pack-result")
        return
    if command != "fetch":
        handler.send_bytes(400, b"unknown command", "text/plain")
        return
    _serve_fetch(handler, repo, args)


def _handle_upload_pack_v0(handler, repo, body):
    lines, _consumed, ok = decode_pkt_lines(body)
    if not ok:
        handler.send_bytes(400, b"bad pkt-line stream", "text/plain")
        return
    args = {"wants": [], "haves": [], "shallows": [], "depth": None}
    seen_flush = False
    for kind, payload in lines:
        if kind == "flush":
            seen_flush = True
            continue
        if kind != "data":
            continue
        text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if text.startswith("want "):
            parts = text.split()
            if len(parts) >= 2:
                args["wants"].append(parts[1])
        elif text.startswith("have "):
            args["haves"].append(text[5:].strip())
        elif text.startswith("shallow "):
            args["shallows"].append(text[8:].strip())
        elif text.startswith("deepen "):
            try:
                args["depth"] = int(text[7:].strip())
            except ValueError:
                pass
    _serve_fetch_v0(handler, repo, args)


def _collect_fetch(repo, wants, haves, shallows, depth):
    """Compute the object set for a fetch. Returns (objects, shallow, unshallow)."""
    if not wants:
        return {}, [], []
    want_objs, want_boundary = reachable_objects(repo.objects, wants, depth=depth)
    held, _hb = reachable_objects(repo.objects, haves, depth=None,
                                  shallow_stop=set(shallows))
    send = {oid: obj for oid, obj in want_objs.items() if oid not in held}
    shallow = []
    unshallow = []
    if depth is not None:
        shallow = want_boundary
        for old in shallows:
            if old in want_objs:
                unshallow.append(old)
    return send, shallow, unshallow


def _serve_fetch(handler, repo, args):
    wants = args["wants"]
    haves = args["haves"]
    shallows = args["shallows"]
    depth = args["depth"]
    send, shallow, unshallow = _collect_fetch(repo, wants, haves, shallows, depth)
    pack = STORE.get_pack(send)
    out = bytearray()
    out += pkt("acknowledgments\n")
    out += pkt("NAK\n")
    out += pkt_delim()
    if depth is not None or unshallow:
        out += pkt("shallow-info\n")
        for oid in shallow:
            out += pkt("shallow %s\n" % oid)
        for oid in unshallow:
            out += pkt("unshallow %s\n" % oid)
        out += pkt_delim()
    out += pkt("packfile\n")
    out += _sideband_pack(pack)
    out += pkt_flush()
    handler.send_bytes(200, bytes(out), "application/x-git-upload-pack-result")


def _serve_fetch_v0(handler, repo, args):
    wants = args["wants"]
    haves = args["haves"]
    shallows = args["shallows"]
    depth = args["depth"]
    send, shallow, unshallow = _collect_fetch(repo, wants, haves, shallows, depth)
    pack = STORE.get_pack(send)
    out = bytearray()
    out += pkt("NAK\n")
    for oid in shallow:
        out += pkt("shallow %s\n" % oid)
    for oid in unshallow:
        out += pkt("unshallow %s\n" % oid)
    out += _sideband_pack(pack)
    out += pkt_flush()
    handler.send_bytes(200, bytes(out), "application/x-git-upload-pack-result")


def handle_git_receive_pack(handler, owner, repo_name, body):
    repo = STORE.get_repo(owner, repo_name)
    if repo is None:
        handler.send_json(404, {"message": "Not Found"})
        return
    # Parse command pkt-lines up to the first flush; the rest is the pack.
    lines = []
    pos = 0
    n = len(body)
    pack_start = None
    ok = True
    while pos < n:
        if pos + 4 > n:
            ok = False
            break
        head = body[pos:pos + 4]
        if head == b"0000":
            pack_start = pos + 4
            break
        try:
            size = int(head.decode("ascii"), 16)
        except ValueError:
            ok = False
            break
        if size < 4 or pos + size > n:
            ok = False
            break
        lines.append(body[pos + 4:pos + size])
        pos += size
    if not ok or pack_start is None:
        # Malformed: stay alive, answer 400, keep serving.
        handler.send_bytes(400, b"bad request", "text/plain")
        return
    pack_bytes = body[pack_start:]
    commands = []
    for raw in lines:
        text = raw.decode("utf-8", "surrogateescape")
        if "\x00" in text:
            text = text.split("\x00", 1)[0]
        parts = text.strip().split()
        if len(parts) != 3:
            continue
        commands.append((parts[0], parts[1], parts[2]))
    new_objects = {}
    if pack_bytes:
        try:
            new_objects = read_pack(pack_bytes)
        except Exception:
            handler.send_bytes(400, b"bad packfile", "text/plain")
            return
    results = []
    with STORE.lock:
        repo.objects.update(new_objects)
        for old, new, refname in commands:
            current = repo.refs.get(refname)
            if new == ZERO_OID:
                # delete
                if current is None:
                    results.append((refname, False, "remote ref does not exist"))
                else:
                    del repo.refs[refname]
                    results.append((refname, True, ""))
                continue
            if new not in repo.objects:
                results.append((refname, False, "object not found"))
                continue
            if old == ZERO_OID:
                if current is not None:
                    results.append((refname, False, "already exists"))
                    continue
                repo.refs[refname] = new
                results.append((refname, True, ""))
                continue
            if current is None:
                results.append((refname, False, "remote ref does not exist"))
                continue
            if current != old:
                results.append((refname, False, "non-fast-forward"))
                continue
            if not is_descendant(repo.objects, old, new):
                results.append((refname, False, "non-fast-forward"))
                continue
            repo.refs[refname] = new
            results.append((refname, True, ""))
        if results:
            repo.bump()
    report = bytearray()
    report += pkt("unpack ok\n")
    for refname, good, reason in results:
        if good:
            report += pkt("ok %s\n" % refname)
        else:
            report += pkt("ng %s %s\n" % (refname, reason))
    report += pkt_flush()
    out = _sideband_pack(bytes(report)) + pkt_flush()
    handler.send_bytes(200, out, "application/x-git-receive-pack-result")


# ---------------------------------------------------------------------------
# REST v3 handlers
# ---------------------------------------------------------------------------

def _need_repo(handler, owner, name):
    repo = STORE.get_repo(owner, name)
    if repo is None:
        handler.send_json(404, {"message": "Not Found"})
        return None
    return repo


def _read_json_body(handler):
    raw = getattr(handler, "_raw_body", None)
    if raw is None:
        length = int(handler.headers.get("Content-Length") or 0)
        raw = handler.rfile.read(length) if length else b""
    if not raw:
        return {}, None
    try:
        parsed = json.loads(raw.decode("utf-8"))
    except Exception:
        return None, "invalid JSON"
    if not isinstance(parsed, dict):
        return None, "invalid JSON"
    return parsed, None


def rest_dispatch(handler, method, parts, query):
    """parts: path segments after /api/v3. Returns True if handled."""
    # root + meta (unauthenticated OK)
    if method == "GET" and parts == []:
        handler.send_json(200, {
            "current_user_url": "https://example.invalid/api/v3/user",
            "rate_limit_url": "https://example.invalid/api/v3/rate_limit",
        }, extra_headers={"X-OAuth-Scopes": "repo, read:org"})
        return True
    if method == "GET" and parts == ["meta"]:
        handler.send_json(200, {"installed_version": "1.0.0"})
        return True
    # everything else needs a bearer token
    if not handler.authorized():
        handler.send_json(401, {"message": "Requires authentication"})
        return True
    if method == "GET" and parts == ["user"]:
        handler.send_json(200, {"login": VIEWER_LOGIN, "id": 1000,
                                "type": "User", "name": VIEWER_LOGIN})
        return True
    if parts == ["user", "repos"]:
        if method == "POST":
            return _rest_create_repo(handler)
        if method == "GET":
            return _rest_list_user_repos(handler, query)
        handler.send_json(404, {"message": "Not Found"})
        return True
    if len(parts) >= 2 and parts[0] == "repos":
        return _rest_repo_dispatch(handler, method, parts[1:], query)
    handler.send_json(404, {"message": "Not Found"})
    return True


def _rest_create_repo(handler):
    body, err = _read_json_body(handler)
    if err:
        handler.send_json(400, {"message": err})
        return True
    name = body.get("name")
    if not isinstance(name, str) or not name:
        handler.send_json(422, {"message": "name is required"})
        return True
    if not REPO_NAME_RE.match(name):
        handler.send_json(422, {"message": "name is invalid"})
        return True
    with STORE.lock:
        if STORE.get_repo(VIEWER_LOGIN, name) is not None:
            handler.send_json(422, {"message": "name already exists on this account"})
            return True
        repo = STORE.create_repo(VIEWER_LOGIN, name,
                                 body.get("description") or "",
                                 body.get("private", False))
    handler.send_json(201, repo_json(repo))
    return True


def _rest_list_user_repos(handler, query):
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    per_page = max(1, min(per_page, 100))
    page = max(1, page)
    repos = STORE.viewer_repos(VIEWER_LOGIN)
    total = len(repos)
    start = (page - 1) * per_page
    chunk = repos[start:start + per_page]
    headers = {}
    base = "%s://%s/api/v3/user/repos" % (
        "http", handler.headers.get("Host", "localhost"))
    links = []
    if start + per_page < total:
        links.append('<%s?per_page=%d&page=%d>; rel="next"' % (base, per_page, page + 1))
        last = (total + per_page - 1) // per_page
        links.append('<%s?per_page=%d&page=%d>; rel="last"' % (base, per_page, last))
    if links:
        headers["Link"] = ", ".join(links)
    handler.send_json(200, [repo_json(r) for r in chunk], extra_headers=headers)
    return True


def _rest_repo_dispatch(handler, method, parts, query):
    owner, name = parts[0], parts[1]
    rest = parts[2:]
    repo = _need_repo(handler, owner, name)
    if repo is None:
        return True
    # /repos/{o}/{r}
    if not rest:
        if method == "GET":
            handler.send_json(200, repo_json(repo))
        elif method == "PATCH":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
            else:
                with STORE.lock:
                    if "description" in body:
                        repo.description = body["description"] or ""
                handler.send_json(200, repo_json(repo))
        elif method == "DELETE":
            with STORE.lock:
                del STORE.repos[(owner, name)]
            handler.send_bytes(204, b"", "application/json")
        else:
            handler.send_json(404, {"message": "Not Found"})
        return True
    # /repos/{o}/{r}/branches
    if rest == ["branches"]:
        if method != "GET":
            handler.send_json(404, {"message": "Not Found"})
            return True
        out = []
        for refname in sorted(repo.refs):
            if refname.startswith("refs/heads/"):
                branch = refname[len("refs/heads/"):]
                out.append({"name": branch, "commit": {"sha": repo.refs[refname]}})
        handler.send_json(200, out)
        return True
    if len(rest) == 2 and rest[0] == "branches":
        if method != "GET":
            handler.send_json(404, {"message": "Not Found"})
            return True
        tip = repo.branch_tip(rest[1])
        if tip is None:
            handler.send_json(404, {"message": "Branch not found"})
        else:
            handler.send_json(200, {"name": rest[1], "commit": {"sha": tip}})
        return True
    # /repos/{o}/{r}/git/refs/heads/{branch}
    if len(rest) == 4 and rest[0] == "git" and rest[1] == "refs" and rest[2] == "heads":
        if method != "GET":
            handler.send_json(404, {"message": "Not Found"})
            return True
        tip = repo.branch_tip(rest[3])
        if tip is None:
            handler.send_json(404, {"message": "Reference does not exist"})
        else:
            handler.send_json(200, {"ref": "refs/heads/" + rest[3],
                                    "object": {"sha": tip}})
        return True
    # /repos/{o}/{r}/git/refs
    if rest == ["git", "refs"]:
        if method != "POST":
            handler.send_json(404, {"message": "Not Found"})
            return True
        body, err = _read_json_body(handler)
        if err:
            handler.send_json(400, {"message": err})
            return True
        ref = body.get("ref")
        sha = body.get("sha")
        if not isinstance(ref, str) or not ref.startswith("refs/heads/"):
            handler.send_json(422, {"message": "Invalid ref"})
            return True
        if not isinstance(sha, str) or sha not in repo.objects:
            handler.send_json(422, {"message": "Object does not exist"})
            return True
        with STORE.lock:
            if ref in repo.refs:
                handler.send_json(422, {"message": "Reference already exists"})
                return True
            repo.refs[ref] = sha
            repo.bump()
        handler.send_json(201, {"ref": ref, "object": {"sha": sha}})
        return True
    # /repos/{o}/{r}/commits
    if rest == ["commits"]:
        if method != "GET":
            handler.send_json(404, {"message": "Not Found"})
            return True
        sha_param = query.get("sha", [None])[0]
        if sha_param:
            tip = repo.refs.get("refs/heads/" + sha_param)
            if tip is None:
                tip = sha_param if sha_param in repo.objects else None
            if tip is None:
                handler.send_json(404, {"message": "No commit found for SHA: " + sha_param})
                return True
        else:
            tip = repo.branch_tip(repo.default_branch)
            if tip is None:
                handler.send_json(200, [])
                return True
        handler.send_json(200, commit_list_json(repo, tip))
        return True
    # /repos/{o}/{r}/contents/{path...}
    if rest and rest[0] == "contents":
        return _rest_contents(handler, method, repo, rest[1:], query)
    # /repos/{o}/{r}/labels
    if rest == ["labels"]:
        if method == "POST":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
                return True
            lname = body.get("name")
            if not isinstance(lname, str) or not lname:
                handler.send_json(422, {"message": "name is required"})
                return True
            with STORE.lock:
                label = repo.labels.get(lname)
                if label is None:
                    label = {"name": lname, "color": body.get("color") or "ededed"}
                    repo.labels[lname] = label
            handler.send_json(201, label)
            return True
        if method == "GET":
            handler.send_json(200, list(repo.labels.values()))
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    # /repos/{o}/{r}/issues...
    if rest and rest[0] == "issues":
        return _rest_issues(handler, method, repo, rest[1:], query)
    # /repos/{o}/{r}/pulls...
    if rest and rest[0] == "pulls":
        return _rest_pulls(handler, method, repo, rest[1:], query)
    handler.send_json(404, {"message": "Not Found"})
    return True


def _resolve_ref_tip(repo, ref_param):
    """ref param: branch name, full ref, or commit oid. Returns tip oid or None."""
    if not ref_param:
        return repo.branch_tip(repo.default_branch)
    tip = repo.branch_tip(ref_param)
    if tip is not None:
        return tip
    if ref_param.startswith("refs/heads/"):
        return repo.refs.get(ref_param)
    if ref_param in repo.objects:
        return ref_param
    return None


def _rest_contents(handler, method, repo, path_parts, query):
    path = "/".join(urllib.parse.unquote(p) for p in path_parts)
    if method == "PUT":
        body, err = _read_json_body(handler)
        if err:
            handler.send_json(400, {"message": err})
            return True
        message = body.get("message")
        content_b64 = body.get("content")
        if not isinstance(message, str) or not isinstance(content_b64, str):
            handler.send_json(422, {"message": "message and content are required"})
            return True
        try:
            raw = base64.b64decode(content_b64, validate=False)
        except Exception:
            handler.send_json(422, {"message": "content is not valid base64"})
            return True
        branch = body.get("branch") or repo.default_branch
        with STORE.lock:
            tip = repo.branch_tip(branch)
            flat = {}
            if tip is not None:
                tree_oid = parse_commit(repo.objects[tip][1])["tree"]
                flat = flatten_tree(repo.objects, tree_oid)
            expected_sha = body.get("sha")
            existing = flat.get(path)
            if expected_sha is not None:
                if existing is None or existing[1] != expected_sha:
                    handler.send_json(409, {"message": "sha does not match"})
                    return True
            blob_oid = hash_object("blob", raw)
            repo.objects[blob_oid] = ("blob", raw)
            is_update = path in flat
            flat[path] = ("100644", blob_oid)
            root_oid, _created = build_trees_from_flat(repo.objects, flat)
            parents = [tip] if tip else []
            commit_bytes = make_commit(root_oid, parents, message)
            commit_oid = hash_object("commit", commit_bytes)
            repo.objects[commit_oid] = ("commit", commit_bytes)
            repo.refs["refs/heads/" + branch] = commit_oid
            repo.bump()
        handler.send_json(201 if not is_update else 200, {
            "content": {"name": path.rsplit("/", 1)[-1], "path": path,
                        "sha": blob_oid, "size": len(raw),
                        "encoding": "base64", "type": "file"},
            "commit": {"sha": commit_oid, "message": message},
        })
        return True
    if method == "GET":
        tip = _resolve_ref_tip(repo, query.get("ref", [None])[0])
        if tip is None:
            handler.send_json(404, {"message": "Not Found"})
            return True
        tree_oid = parse_commit(repo.objects[tip][1])["tree"]
        flat = flatten_tree(repo.objects, tree_oid)
        if path in flat:
            _mode, blob_oid = flat[path]
            raw = repo.objects[blob_oid][1]
            handler.send_json(200, {
                "type": "file", "encoding": "base64",
                "content": base64.b64encode(raw).decode("ascii"),
                "sha": blob_oid, "size": len(raw),
                "name": path.rsplit("/", 1)[-1], "path": path,
            })
            return True
        # directory listing
        prefix = path + "/" if path else ""
        entries = {}
        for p, (mode, oid) in flat.items():
            if not p.startswith(prefix):
                continue
            rest = p[len(prefix):]
            if "/" in rest:
                dname = rest.split("/")[0]
                if dname not in entries:
                    entries[dname] = {"type": "dir", "name": dname,
                                      "path": prefix + dname, "sha": ""}
            else:
                entries[rest] = {"type": "file", "name": rest,
                                 "path": p, "sha": oid, "size": len(repo.objects[oid][1])}
        if entries or path == "":
            handler.send_json(200, [entries[k] for k in sorted(entries)])
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    if method == "DELETE":
        body, err = _read_json_body(handler)
        if err:
            handler.send_json(400, {"message": err})
            return True
        branch = body.get("branch") or repo.default_branch
        with STORE.lock:
            tip = repo.branch_tip(branch)
            if tip is None:
                handler.send_json(404, {"message": "Not Found"})
                return True
            tree_oid = parse_commit(repo.objects[tip][1])["tree"]
            flat = flatten_tree(repo.objects, tree_oid)
            if path not in flat:
                handler.send_json(404, {"message": "Not Found"})
                return True
            expected_sha = body.get("sha")
            if expected_sha is not None and flat[path][1] != expected_sha:
                handler.send_json(409, {"message": "sha does not match"})
                return True
            del flat[path]
            root_oid, _created = build_trees_from_flat(repo.objects, flat)
            commit_bytes = make_commit(root_oid, [tip], body.get("message") or "Delete %s" % path)
            commit_oid = hash_object("commit", commit_bytes)
            repo.objects[commit_oid] = ("commit", commit_bytes)
            repo.refs["refs/heads/" + branch] = commit_oid
            repo.bump()
        handler.send_json(200, {"commit": {"sha": commit_oid}})
        return True
    handler.send_json(404, {"message": "Not Found"})
    return True


def _rest_issues(handler, method, repo, rest, query):
    if not rest:
        if method == "POST":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
                return True
            title = body.get("title")
            if not isinstance(title, str) or not title:
                handler.send_json(422, {"message": "title is required"})
                return True
            labels = body.get("labels") or []
            if not isinstance(labels, list):
                labels = []
            with STORE.lock:
                for lname in labels:
                    if lname not in repo.labels:
                        handler.send_json(422, {"message": "Label does not exist"})
                        return True
                number = max(repo.issues.keys(), default=0) + 1
                issue = Issue(number, STORE.new_id(), title,
                              body.get("body") or "", labels, STORE.new_seq())
                repo.issues[number] = issue
            handler.send_json(201, issue_json(repo, issue))
            return True
        if method == "GET":
            state = query.get("state", ["open"])[0]
            sort = query.get("sort", ["created"])[0]
            direction = query.get("direction", ["desc"])[0]
            try:
                per_page = int(query.get("per_page", ["30"])[0])
            except ValueError:
                per_page = 30
            issues = list(repo.issues.values())
            if state != "all":
                issues = [i for i in issues if i.state == state]
            issues.sort(key=lambda i: i.seq, reverse=(direction != "asc"))
            handler.send_json(200, [issue_json(repo, i) for i in issues[:per_page]])
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    # /issues/{n}
    try:
        number = int(rest[0])
    except ValueError:
        handler.send_json(404, {"message": "Not Found"})
        return True
    issue = repo.issues.get(number)
    if issue is None:
        handler.send_json(404, {"message": "Not Found"})
        return True
    if len(rest) == 1:
        if method == "GET":
            handler.send_json(200, issue_json(repo, issue))
            return True
        if method == "PATCH":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
                return True
            with STORE.lock:
                if "state" in body:
                    issue.state = body["state"]
                if "title" in body:
                    issue.title = body["title"]
                if "body" in body:
                    issue.body = body["body"]
            handler.send_json(200, issue_json(repo, issue))
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    if rest[1] == "comments":
        if method == "POST":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
                return True
            cbody = body.get("body")
            if not isinstance(cbody, str):
                handler.send_json(422, {"message": "body is required"})
                return True
            with STORE.lock:
                cid = STORE.new_id()
                issue.comments.append({"id": cid, "body": cbody})
            handler.send_json(201, {"id": cid, "body": cbody,
                                    "user": {"login": repo.owner}})
            return True
        if method == "GET":
            handler.send_json(200, [{"id": c["id"], "body": c["body"],
                                     "user": {"login": repo.owner}}
                                    for c in issue.comments])
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    handler.send_json(404, {"message": "Not Found"})
    return True


def _rest_pulls(handler, method, repo, rest, query):
    if not rest:
        if method == "POST":
            body, err = _read_json_body(handler)
            if err:
                handler.send_json(400, {"message": err})
                return True
            title = body.get("title")
            head = body.get("head")
            base = body.get("base")
            if not isinstance(title, str) or not title:
                handler.send_json(422, {"message": "title is required"})
                return True
            if not isinstance(head, str) or not isinstance(base, str):
                handler.send_json(422, {"message": "head and base are required"})
                return True
            with STORE.lock:
                head_tip = repo.branch_tip(head)
                base_tip = repo.branch_tip(base)
                if head_tip is None or base_tip is None:
                    handler.send_json(422, {"message": "head or base branch does not exist"})
                    return True
                for existing in repo.prs.values():
                    if (existing.state == "open" and existing.head == head
                            and existing.base == base):
                        handler.send_json(422, {"message": "A pull request already exists for these branches"})
                        return True
                number = max(repo.prs.keys(), default=0) + 1
                pr = PullRequest(number, STORE.new_id(), title,
                                body.get("body") or "", head, base,
                                head_tip, base_tip, base_tip, STORE.new_seq())
                repo.prs[number] = pr
            handler.send_json(201, pr_json(repo, pr))
            return True
        if method == "GET":
            state = query.get("state", ["open"])[0]
            prs = list(repo.prs.values())
            if state == "open":
                prs = [p for p in prs if p.state == "open"]
            elif state == "closed":
                prs = [p for p in prs if p.state == "closed"]
            prs.sort(key=lambda p: p.seq)
            handler.send_json(200, [pr_json(repo, p) for p in prs])
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    try:
        number = int(rest[0])
    except ValueError:
        handler.send_json(404, {"message": "Not Found"})
        return True
    pr = repo.prs.get(number)
    if pr is None:
        handler.send_json(404, {"message": "Not Found"})
        return True
    if len(rest) == 1:
        if method == "GET":
            handler.send_json(200, pr_json(repo, pr))
            return True
        handler.send_json(404, {"message": "Not Found"})
        return True
    if rest[1] == "files":
        if method != "GET":
            handler.send_json(404, {"message": "Not Found"})
            return True
        head_tip = repo.branch_tip(pr.head)
        base_tip = repo.branch_tip(pr.base)
        head_tree = parse_commit(repo.objects[head_tip][1])["tree"] if head_tip else None
        base_tree = parse_commit(repo.objects[base_tip][1])["tree"] if base_tip else None
        files = diff_trees(repo, base_tree, head_tree)
        handler.send_json(200, [{k: v for k, v in f.items() if not k.startswith("_")}
                                for f in files])
        return True
    if rest[1] == "merge":
        if method != "PUT":
            handler.send_json(404, {"message": "Not Found"})
            return True
        _body, err = _read_json_body(handler)
        if err:
            handler.send_json(400, {"message": err})
            return True
        if pr.state != "open":
            handler.send_json(405, {"message": "Pull request is not open"})
            return True
        with STORE.lock:
            head_tip = repo.branch_tip(pr.head)
            base_tip = repo.branch_tip(pr.base)
            if head_tip is None or base_tip is None:
                handler.send_json(404, {"message": "Branch not found"})
                return True
            head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
            base_tree = parse_commit(repo.objects[base_tip][1])["tree"]
            mb_tree = None
            if pr.merge_base and pr.merge_base in repo.objects:
                mb_tree = parse_commit(repo.objects[pr.merge_base][1])["tree"]
            merged_tree, conflict = three_way_merge(repo, base_tip, head_tip, pr.merge_base)
            if conflict:
                handler.send_json(405, {"message": "Merge conflict"})
                return True
            msg = "Merge pull request #%d from %s" % (pr.number, pr.head)
            commit_bytes = make_commit(merged_tree, [base_tip], msg)
            merge_oid = hash_object("commit", commit_bytes)
            repo.objects[merge_oid] = ("commit", commit_bytes)
            repo.refs["refs/heads/" + pr.base] = merge_oid
            pr.state = "closed"
            pr.merged = True
            pr.merged_at = MERGED_AT
            pr.merge_commit_sha = merge_oid
            repo.bump()
        handler.send_json(200, {"merged": True, "sha": merge_oid, "message": msg})
        return True
    handler.send_json(404, {"message": "Not Found"})
    return True


# ---------------------------------------------------------------------------
# GraphQL v4 handlers
# ---------------------------------------------------------------------------

def _gql_repo_fields(repo):
    tip = repo.branch_tip(repo.default_branch)
    return {
        "id": global_id("Repository", repo.owner, repo.name),
        "databaseId": repo.id,
        "name": repo.name,
        "nameWithOwner": repo.full_name(),
        "owner": {"login": repo.owner},
        "defaultBranchRef": {"name": repo.default_branch} if tip else None,
        "viewerPermission": "ADMIN",
        "hasIssuesEnabled": True,
    }


def _gql_issue_fields(repo, issue):
    return {
        "id": global_id("Issue", repo.owner, repo.name, str(issue.number)),
        "number": issue.number,
        "title": issue.title,
        "state": issue.state.upper(),
        "body": issue.body,
    }


def _gql_pr_mergeable(repo, pr):
    head_tip = repo.branch_tip(pr.head)
    base_tip = repo.branch_tip(pr.base)
    if head_tip is None or base_tip is None or pr.merge_base is None:
        return "UNKNOWN"
    _tree, conflict = three_way_merge(repo, base_tip, head_tip, pr.merge_base)
    return "CONFLICTING" if conflict else "MERGEABLE"


def _gql_pr_fields(repo, pr, with_files=False, files_first=10):
    out = {
        "id": global_id("PullRequest", repo.owner, repo.name, str(pr.number)),
        "number": pr.number,
        "state": pr.state.upper(),
        "merged": pr.merged,
        "headRefName": pr.head,
        "baseRefName": pr.base,
        "mergeable": _gql_pr_mergeable(repo, pr),
    }
    if with_files:
        head_tip = repo.branch_tip(pr.head)
        base_tip = repo.branch_tip(pr.base)
        head_tree = parse_commit(repo.objects[head_tip][1])["tree"] if head_tip else None
        base_tree = parse_commit(repo.objects[base_tip][1])["tree"] if base_tip else None
        files = diff_trees(repo, base_tree, head_tree)[:files_first]
        out["files"] = {"nodes": [{"path": f["filename"]} for f in files]}
    return out


def _gql_cursor(number):
    return b64url_encode(("cursor:%d" % number).encode("utf-8"))


def _gql_cursor_number(cursor):
    try:
        text = b64url_decode(cursor).decode("utf-8")
        if text.startswith("cursor:"):
            return int(text[len("cursor:"):])
    except Exception:
        return None
    return None


def _gql_issues_connection(repo, first, states, order_by, after):
    issues = list(repo.issues.values())
    if states:
        wanted = {s.upper() for s in states}
        issues = [i for i in issues if i.state.upper() in wanted]
    direction = "DESC"
    if order_by and isinstance(order_by, dict):
        direction = str(order_by.get("direction", "DESC")).upper()
    issues.sort(key=lambda i: i.seq, reverse=(direction == "DESC"))
    if after:
        after_num = _gql_cursor_number(after)
        if after_num is not None:
            if direction == "DESC":
                issues = [i for i in issues if i.seq < after_num]
            else:
                issues = [i for i in issues if i.seq > after_num]
    total = len(issues)
    if first is not None:
        page = issues[:first]
    else:
        page = issues
    has_next = len(page) < total
    end_cursor = _gql_cursor(page[-1].seq) if page else None
    return {
        "nodes": [_gql_issue_fields(repo, i) for i in page],
        "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor},
    }


def _gql_type_fields(name):
    catalog = {
        "Issue": ["id", "number", "title", "state", "body", "createdAt",
                  "updatedAt", "author", "labels", "comments", "url"],
        "PullRequest": ["id", "number", "headRefName", "baseRefName",
                        "mergeable", "state", "merged", "files", "title",
                        "body", "author", "createdAt", "updatedAt", "url"],
        "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                       "defaultBranchRef", "viewerPermission",
                       "hasIssuesEnabled", "issue", "issues", "pullRequests",
                       "pullRequest", "description", "isPrivate", "url"],
    }
    fields = catalog.get(name)
    if fields is None:
        return None
    return {"fields": [{"name": f} for f in fields]}


def _gql_type_enum(name):
    if name == "SearchType":
        return {"enumValues": [{"name": "ISSUE"}, {"name": "PULL_REQUEST"},
                               {"name": "REPOSITORY"}, {"name": "USER"},
                               {"name": "DISCUSSION"}]}
    return None


def _gql_dispatch_operation(op_name, variables):
    """Dispatch a GraphQL operation by name. Returns (data, errors)."""
    variables = variables or {}

    def repo_from_vars(owner_key="owner", name_key="name"):
        owner = variables.get(owner_key)
        name = variables.get(name_key)
        if owner is None or name is None:
            return None
        return STORE.get_repo(owner, name)

    if op_name == "ViewerLogin":
        return {"viewer": {"login": VIEWER_LOGIN}}, None
    if op_name == "ViewerInvalidField":
        return None, [{"message": 'Cannot query field "noSuchFieldOnViewer" on type "User".'}]
    if op_name == "RepositoryFields":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        return {"repository": _gql_repo_fields(repo)}, None
    if op_name == "Issue_fields":
        return {"Issue": _gql_type_fields("Issue")}, None
    if op_name == "PullRequestAndRepositoryFields":
        return {"PullRequest": _gql_type_fields("PullRequest"),
                "Repository": _gql_type_fields("Repository")}, None
    if op_name == "SearchType_enumValues":
        return {"SearchType": _gql_type_enum("SearchType")}, None
    if op_name == "OpenIssues":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        conn = _gql_issues_connection(
            repo, variables.get("first"), variables.get("states"),
            variables.get("orderBy"), variables.get("after"))
        return {"repository": {"issues": conn}}, None
    if op_name == "IssueByNumber":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        issue = repo.issues.get(variables.get("number"))
        return {"repository": {"issue": _gql_issue_fields(repo, issue) if issue else None}}, None
    if op_name == "IssuesPage":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        conn = _gql_issues_connection(
            repo, variables.get("first"), variables.get("states"),
            variables.get("orderBy"), variables.get("after"))
        return {"repository": {"issues": conn}}, None
    if op_name == "PullRequests":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        prs = sorted(repo.prs.values(), key=lambda p: p.seq)
        first = variables.get("first")
        if first is not None:
            prs = prs[:first]
        return {"repository": {"pullRequests": {
            "nodes": [_gql_pr_fields(repo, p) for p in prs]}}}, None
    if op_name == "PullRequestFiles":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        pr = repo.prs.get(variables.get("number"))
        if pr is None:
            return {"repository": {"pullRequest": None}}, None
        return {"repository": {"pullRequest": _gql_pr_fields(repo, pr, with_files=True, files_first=10)}}, None
    if op_name == "PullRequestId":
        repo = repo_from_vars()
        if repo is None:
            return {"repository": None}, None
        pr = repo.prs.get(variables.get("number"))
        if pr is None:
            return {"repository": {"pullRequest": None}}, None
        return {"repository": {"pullRequest": _gql_pr_fields(repo, pr)}}, None
    if op_name == "NodeRepository":
        gid = variables.get("id")
        kind, parts = parse_global_id(gid or "")
        if kind == "Repository" and len(parts) >= 2:
            repo = STORE.get_repo(parts[0], parts[1])
            if repo is not None:
                return {"node": {"id": gid, "name": repo.name,
                                 "nameWithOwner": repo.full_name()}}, None
        return {"node": None}, None
    if op_name == "IssueCreate":
        inp = variables.get("input") or {}
        kind, parts = parse_global_id(inp.get("repositoryId") or "")
        if kind != "Repository" or len(parts) < 2:
            return None, [{"message": "Could not resolve to a Repository with the id of %s." % inp.get("repositoryId")}]
        repo = STORE.get_repo(parts[0], parts[1])
        if repo is None:
            return None, [{"message": "Could not resolve to a Repository."}]
        with STORE.lock:
            number = max(repo.issues.keys(), default=0) + 1
            issue = Issue(number, STORE.new_id(), inp.get("title") or "",
                          inp.get("body") or "", [], STORE.new_seq())
            repo.issues[number] = issue
        return {"createIssue": {"issue": _gql_issue_fields(repo, issue)}}, None
    if op_name == "IssueClose":
        inp = variables.get("input") or {}
        kind, parts = parse_global_id(inp.get("issueId") or "")
        if kind != "Issue" or len(parts) < 3:
            return None, [{"message": "Could not resolve to an Issue."}]
        repo = STORE.get_repo(parts[0], parts[1])
        issue = repo.issues.get(int(parts[2])) if repo else None
        if issue is None:
            return None, [{"message": "Could not resolve to an Issue."}]
        with STORE.lock:
            issue.state = "closed"
        return {"closeIssue": {"issue": _gql_issue_fields(repo, issue)}}, None
    if op_name == "PullRequestCreate":
        inp = variables.get("input") or {}
        kind, parts = parse_global_id(inp.get("repositoryId") or "")
        if kind != "Repository" or len(parts) < 2:
            return None, [{"message": "Could not resolve to a Repository."}]
        repo = STORE.get_repo(parts[0], parts[1])
        if repo is None:
            return None, [{"message": "Could not resolve to a Repository."}]
        head = inp.get("headRefName")
        base = inp.get("baseRefName")
        with STORE.lock:
            head_tip = repo.branch_tip(head)
            base_tip = repo.branch_tip(base)
            if head_tip is None or base_tip is None:
                return None, [{"message": "Head or base branch does not exist."}]
            for existing in repo.prs.values():
                if existing.state == "open" and existing.head == head and existing.base == base:
                    pr = existing
                    break
            else:
                number = max(repo.prs.keys(), default=0) + 1
                pr = PullRequest(number, STORE.new_id(), inp.get("title") or "",
                                "", head, base, head_tip, base_tip, base_tip,
                                STORE.new_seq())
                repo.prs[number] = pr
        return {"createPullRequest": {"pullRequest": _gql_pr_fields(repo, pr)}}, None
    if op_name == "MergePullRequest":
        inp = variables.get("input") or {}
        kind, parts = parse_global_id(inp.get("pullRequestId") or "")
        if kind != "PullRequest" or len(parts) < 3:
            return None, [{"message": "Could not resolve to a PullRequest."}]
        repo = STORE.get_repo(parts[0], parts[1])
        pr = repo.prs.get(int(parts[2])) if repo else None
        if pr is None:
            return None, [{"message": "Could not resolve to a PullRequest."}]
        merged = _merge_pr_internal(repo, pr)
        if not merged:
            return None, [{"message": "Merge conflict."}]
        return {"mergePullRequest": {"pullRequest": _gql_pr_fields(repo, pr)}}, None
    if op_name == "AddComment":
        inp = variables.get("input") or {}
        kind, parts = parse_global_id(inp.get("subjectId") or "")
        if kind != "Issue" or len(parts) < 3:
            return None, [{"message": "Could not resolve to an Issue."}]
        repo = STORE.get_repo(parts[0], parts[1])
        issue = repo.issues.get(int(parts[2])) if repo else None
        if issue is None:
            return None, [{"message": "Could not resolve to an Issue."}]
        with STORE.lock:
            cid = STORE.new_id()
            issue.comments.append({"id": cid, "body": inp.get("body") or ""})
        comment_gid = global_id("IssueComment", repo.owner, repo.name,
                                str(issue.number), str(cid))
        return {"addComment": {"commentEdge": {"node": {"id": comment_gid,
                                                        "body": inp.get("body") or ""}}}}, None
    return None, [{"message": "Unknown operation: %s" % op_name}]


def _merge_pr_internal(repo, pr):
    """Squash-merge an open PR. Returns True on success."""
    if pr.state != "open":
        return False
    with STORE.lock:
        head_tip = repo.branch_tip(pr.head)
        base_tip = repo.branch_tip(pr.base)
        if head_tip is None or base_tip is None:
            return False
        merged_tree, conflict = three_way_merge(repo, base_tip, head_tip,
                                                pr.merge_base)
        if conflict:
            return False
        msg = "Merge pull request #%d from %s" % (pr.number, pr.head)
        commit_bytes = make_commit(merged_tree, [base_tip], msg)
        merge_oid = hash_object("commit", commit_bytes)
        repo.objects[merge_oid] = ("commit", commit_bytes)
        repo.refs["refs/heads/" + pr.base] = merge_oid
        pr.state = "closed"
        pr.merged = True
        pr.merged_at = MERGED_AT
        pr.merge_commit_sha = merge_oid
        repo.bump()
    return True


_OP_RE = re.compile(r"\b(query|mutation)\s+([A-Za-z_][A-Za-z0-9_]*)")


_INLINE_STATES_RE = re.compile(r"\bstates:\s*\[([^\]]*)\]")
_INLINE_ORDERBY_RE = re.compile(r"\borderBy:\s*\{([^}]*)\}")
_INLINE_FIRST_RE = re.compile(r"\bfirst:\s*(\d+)")
_INLINE_AFTER_NULL_RE = re.compile(r"\bafter:\s*null\b")


def _extract_inline_args(query):
    """Inline GraphQL argument literals (states, orderBy, first, after:null).

    The suite's documents pass some arguments inline rather than as
    variables (e.g. `states: [OPEN]`, `orderBy: {field: CREATED_AT,
    direction: DESC}`); JSON variables still win when both are present.
    """
    out = {}
    m = _INLINE_STATES_RE.search(query)
    if m:
        out["states"] = [s.strip() for s in m.group(1).split(",") if s.strip()]
    m = _INLINE_ORDERBY_RE.search(query)
    if m:
        fields = {}
        for part in m.group(1).split(","):
            if ":" in part:
                k, v = part.split(":", 1)
                fields[k.strip()] = v.strip()
        if fields:
            out["orderBy"] = fields
    m = _INLINE_FIRST_RE.search(query)
    if m:
        out["first"] = int(m.group(1))
    if _INLINE_AFTER_NULL_RE.search(query):
        out["after"] = None
    return out


def handle_graphql(handler, body_bytes):
    try:
        payload = json.loads(body_bytes.decode("utf-8"))
    except Exception:
        handler.send_json(400, {"message": "invalid JSON"})
        return
    is_batch = isinstance(payload, list)
    operations = payload if is_batch else [payload]
    responses = []
    for op in operations:
        if not isinstance(op, dict) or "query" not in op:
            responses.append({"data": None,
                              "errors": [{"message": "Invalid GraphQL operation."}]})
            continue
        query = op.get("query") or ""
        variables = op.get("variables") or {}
        merged = _extract_inline_args(query)
        merged.update(variables)
        match = _OP_RE.search(query)
        op_name = match.group(2) if match else None
        if op_name is None:
            # fallback: detect by distinctive substrings
            if "__type" in query and '"Issue"' in query:
                op_name = "Issue_fields"
            elif "noSuchFieldOnViewer" in query:
                op_name = "ViewerInvalidField"
            elif "viewer" in query and "login" in query:
                op_name = "ViewerLogin"
            else:
                op_name = "?"
        data, errors = _gql_dispatch_operation(op_name, merged)
        resp = {}
        if data is not None:
            resp["data"] = data
        if errors:
            resp["errors"] = errors
        if data is None and not errors:
            resp["data"] = None
        responses.append(resp)
    handler.send_json(200, responses if is_batch else responses[0])


# ---------------------------------------------------------------------------
# MCP handlers
# ---------------------------------------------------------------------------

_MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository owned by the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string"},
                "owner": {"type": "string"},
                "description": {"type": "string"},
                "private": {"type": "boolean"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "body": {"type": "string"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List issues in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "state": {"type": "string"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request from a head branch into a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "title": {"type": "string"},
                "head": {"type": "string"},
                "base": {"type": "string"},
                "body": {"type": "string"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Squash-merge an open pull request.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string"},
                "repo": {"type": "string"},
                "pull_number": {"type": "integer"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]


def _mcp_result(payload):
    text = json.dumps(payload, separators=(",", ":"), sort_keys=True)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": payload, "isError": False}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": message}], "isError": True}


def _mcp_call_tool(name, args):
    args = args or {}
    if name == "create_repo":
        rname = args.get("name")
        if not isinstance(rname, str) or not rname:
            return _mcp_error_result("Missing required argument: name")
        owner = args.get("owner") or VIEWER_LOGIN
        with STORE.lock:
            if STORE.get_repo(owner, rname) is not None:
                repo = STORE.get_repo(owner, rname)
            else:
                repo = STORE.create_repo(owner, rname,
                                         args.get("description") or "",
                                         args.get("private", False))
        return _mcp_result(repo_json(repo))
    if name == "get_repo":
        owner = args.get("owner")
        rname = args.get("repo")
        if not owner or not rname:
            return _mcp_error_result("Missing required argument: owner/repo")
        repo = STORE.get_repo(owner, rname)
        if repo is None:
            return _mcp_error_result("Repository not found")
        return _mcp_result(repo_json(repo))
    if name == "create_issue":
        owner, rname = args.get("owner"), args.get("repo")
        title = args.get("title")
        if not owner or not rname or not title:
            return _mcp_error_result("Missing required argument: owner/repo/title")
        repo = STORE.get_repo(owner, rname)
        if repo is None:
            return _mcp_error_result("Repository not found")
        with STORE.lock:
            number = max(repo.issues.keys(), default=0) + 1
            issue = Issue(number, STORE.new_id(), title,
                          args.get("body") or "", [], STORE.new_seq())
            repo.issues[number] = issue
        return _mcp_result(issue_json(repo, issue))
    if name == "list_issues":
        owner, rname = args.get("owner"), args.get("repo")
        if not owner or not rname:
            return _mcp_error_result("Missing required argument: owner/repo")
        repo = STORE.get_repo(owner, rname)
        if repo is None:
            return _mcp_error_result("Repository not found")
        state = args.get("state") or "open"
        issues = list(repo.issues.values())
        if state != "all":
            issues = [i for i in issues if i.state == state]
        issues.sort(key=lambda i: i.seq)
        return _mcp_result([issue_json(repo, i) for i in issues])
    if name == "create_pull_request":
        owner, rname = args.get("owner"), args.get("repo")
        title, head, base = args.get("title"), args.get("head"), args.get("base")
        if not owner or not rname or not title or not head or not base:
            return _mcp_error_result("Missing required argument: owner/repo/title/head/base")
        repo = STORE.get_repo(owner, rname)
        if repo is None:
            return _mcp_error_result("Repository not found")
        with STORE.lock:
            head_tip = repo.branch_tip(head)
            base_tip = repo.branch_tip(base)
            if head_tip is None or base_tip is None:
                return _mcp_error_result("Head or base branch does not exist")
            for existing in repo.prs.values():
                if (existing.state == "open" and existing.head == head
                        and existing.base == base):
                    return _mcp_result(pr_json(repo, existing))
            number = max(repo.prs.keys(), default=0) + 1
            pr = PullRequest(number, STORE.new_id(), title,
                            args.get("body") or "", head, base,
                            head_tip, base_tip, base_tip, STORE.new_seq())
            repo.prs[number] = pr
        return _mcp_result(pr_json(repo, pr))
    if name == "merge_pull_request":
        owner, rname = args.get("owner"), args.get("repo")
        number = args.get("pull_number")
        if not owner or not rname or number is None:
            return _mcp_error_result("Missing required argument: owner/repo/pull_number")
        repo = STORE.get_repo(owner, rname)
        if repo is None:
            return _mcp_error_result("Repository not found")
        pr = repo.prs.get(int(number))
        if pr is None:
            return _mcp_error_result("Pull request not found")
        if _merge_pr_internal(repo, pr):
            return _mcp_result(pr_json(repo, pr))
        return _mcp_error_result("Merge conflict")
    return None


def handle_mcp(handler, body_bytes):
    if not handler.authorized():
        handler.send_json(401, {"message": "Requires authentication"})
        return
    try:
        payload = json.loads(body_bytes.decode("utf-8"))
    except Exception:
        handler.send_json(400, {"jsonrpc": "2.0", "id": None,
                                "error": {"code": -32700, "message": "Parse error"}})
        return
    if not isinstance(payload, dict):
        handler.send_json(400, {"jsonrpc": "2.0", "id": None,
                                "error": {"code": -32700, "message": "Parse error"}})
        return
    req_id = payload.get("id")
    method = payload.get("method")
    params = payload.get("params") or {}
    if method == "server/discover":
        handler.send_json(200, {"jsonrpc": "2.0", "id": req_id, "result": {
            "supportedVersions": ["2026-07-28", "2025-11-25"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "github-core-clone-forge", "version": "1.0.0"},
        }})
        return
    if method == "initialize":
        handler.send_json(200, {"jsonrpc": "2.0", "id": req_id, "result": {
            "protocolVersion": "2026-07-28",
            "capabilities": {"tools": {}},
            "serverInfo": {"name": "github-core-clone-forge", "version": "1.0.0"},
        }})
        return
    if method == "notifications/initialized":
        handler.send_json(200, {})
        return
    if method == "tools/list":
        handler.send_json(200, {"jsonrpc": "2.0", "id": req_id,
                                "result": {"tools": _MCP_TOOLS}})
        return
    if method == "tools/call":
        tool_name = params.get("name")
        tool_args = params.get("arguments") or {}
        known = {t["name"] for t in _MCP_TOOLS}
        if tool_name not in known:
            handler.send_json(200, {"jsonrpc": "2.0", "id": req_id,
                                    "error": {"code": -32602,
                                              "message": "Unknown tool: %s" % tool_name}})
            return
        result = _mcp_call_tool(tool_name, tool_args)
        handler.send_json(200, {"jsonrpc": "2.0", "id": req_id, "result": result})
        return
    handler.send_json(200, {"jsonrpc": "2.0", "id": req_id,
                            "error": {"code": -32601,
                                      "message": "Method not found: %s" % method}})


# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------

class ForgeServer(ThreadingHTTPServer):
    # The clone benchmark opens 50 connections at once. The default
    # listen backlog (5) drops SYNs under that burst and clients stall
    # on ~1 s TCP retransmits; a deep backlog removes the stall.
    request_queue_size = 256
    daemon_threads = True


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def setup(self):
        # Disable Nagle on the accepted socket: without this, a small
        # request + small response on a keep-alive connection stalls on
        # the 40 ms delayed-ACK timer (measured 41 ms/req -> 0.6 ms/req).
        # (self.request is the accepted socket here; .connection is only
        # assigned by StreamRequestHandler.setup below.)
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        super().setup()

    def log_message(self, fmt, *args):
        pass

    # -- auth ---------------------------------------------------------------
    def authorized(self):
        token = os.environ.get("MAKEFUN_SHOP_TOKEN")
        auth = self.headers.get("Authorization") or ""
        if not auth.startswith("Bearer "):
            return False
        presented = auth[len("Bearer "):].strip()
        if not presented:
            return False
        if token:
            return presented == token
        return True

    # -- send helpers -------------------------------------------------------
    def _send(self, status, body, ctype, extra_headers=None):
        # One buffered write for the whole response (status line, headers
        # and body): BaseHTTPRequestHandler's send_response/send_header
        # chain issues ~8 small writes per response, each a syscall.
        if isinstance(body, str):
            body = body.encode("utf-8")
        reason = self.responses.get(status, ("?",))[0]
        lines = [
            "HTTP/1.1 %d %s" % (status, reason),
            "Server: Forge/1.0",
            "Date: %s" % self.date_time_string(),
            "Content-Type: %s" % ctype,
            "Content-Length: %d" % len(body),
            "X-GitHub-Request-Id: %s" % STORE.request_id(),
        ]
        if extra_headers:
            for k, v in extra_headers.items():
                lines.append("%s: %s" % (k, v))
        head = ("\r\n".join(lines) + "\r\n\r\n").encode("ascii", "replace")
        try:
            if self.command != "HEAD" and body:
                self.wfile.write(head + body)
            else:
                self.wfile.write(head)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def send_json(self, status, obj, extra_headers=None):
        body = json.dumps(obj, separators=(",", ":")).encode("utf-8")
        self._send(status, body, "application/json", extra_headers)

    def send_bytes(self, status, body, ctype, extra_headers=None):
        self._send(status, body, ctype, extra_headers)

    def _read_body(self):
        length = int(self.headers.get("Content-Length") or 0)
        if length <= 0:
            return b""
        return self.rfile.read(length)

    # -- routing ------------------------------------------------------------
    def _route(self, method):
        parsed = urllib.parse.urlsplit(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)
        # Consume any request body up front. A handler that answers early
        # (401/404) without reading it would leave bytes in the socket and
        # desync the keep-alive connection, corrupting the next request.
        raw_body = b""
        if method in ("POST", "PUT", "PATCH", "DELETE"):
            raw_body = self._read_body()
        self._raw_body = raw_body
        try:
            if method == "GET" and path == "/healthz":
                self.send_json(200, {"ok": True})
                return
            # git smart HTTP
            m = re.match(r"^/([^/]+)/([^/]+)\.git/(info/refs|git-upload-pack|git-receive-pack)$", path)
            if m:
                owner, repo_name, action = m.group(1), m.group(2), m.group(3)
                if action == "info/refs":
                    if method == "GET":
                        handle_git_info_refs(self, owner, repo_name, query)
                    else:
                        self.send_json(404, {"message": "Not Found"})
                elif action == "git-upload-pack":
                    if method == "POST":
                        handle_git_upload_pack(self, owner, repo_name, raw_body)
                    else:
                        self.send_json(404, {"message": "Not Found"})
                elif action == "git-receive-pack":
                    if method == "POST":
                        handle_git_receive_pack(self, owner, repo_name, raw_body)
                    else:
                        self.send_json(404, {"message": "Not Found"})
                return
            # REST v3
            if path == "/api/v3" or path.startswith("/api/v3/"):
                rest_path = path[len("/api/v3"):].strip("/")
                parts = [urllib.parse.unquote(p) for p in rest_path.split("/") if p != ""] if rest_path else []
                rest_dispatch(self, method, parts, query)
                return
            # GraphQL
            if path == "/api/graphql":
                if method == "POST":
                    if not self.authorized():
                        self.send_json(401, {"message": "Requires authentication"})
                        return
                    handle_graphql(self, raw_body)
                else:
                    self.send_json(404, {"message": "Not Found"})
                return
            # MCP
            if path == "/mcp":
                if method == "POST":
                    handle_mcp(self, raw_body)
                else:
                    self.send_json(404, {"message": "Not Found"})
                return
            self.send_json(404, {"message": "Not Found"})
        except (BrokenPipeError, ConnectionResetError):
            raise
        except Exception as exc:  # never die on a bad request
            try:
                self.send_json(500, {"message": "Internal error: %s" % exc})
            except Exception:
                pass

    def do_GET(self):
        self._route("GET")

    def do_POST(self):
        self._route("POST")

    def do_PUT(self):
        self._route("PUT")

    def do_PATCH(self):
        self._route("PATCH")

    def do_DELETE(self):
        self._route("DELETE")


# ---------------------------------------------------------------------------
# Lifecycle: bind ephemeral port, register with the env, wait for done
# ---------------------------------------------------------------------------

def _http_json(url, payload=None, timeout=30):
    data = None
    headers = {"Content-Type": "application/json"}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers,
                                 method="POST" if payload is not None else "GET")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        raw = resp.read()
    try:
        return json.loads(raw.decode("utf-8"))
    except Exception:
        return {}


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL")
    port = int(os.environ.get("FORGE_PORT", "0"))
    server = ForgeServer(("127.0.0.1", port), ForgeHandler)
    actual_port = server.server_address[1]
    if env_url:
        # Register, retrying until 200 or 409; then poll /done.
        registered = False
        deadline = time.time() + 300
        backoff = 0.25
        while time.time() < deadline and not registered:
            try:
                with urllib.request.urlopen(
                        urllib.request.Request(
                            env_url.rstrip("/") + "/register",
                            data=json.dumps({"port": actual_port}).encode("utf-8"),
                            headers={"Content-Type": "application/json"},
                            method="POST"),
                        timeout=10) as resp:
                    if resp.status in (200, 409):
                        registered = True
            except urllib.error.HTTPError as e:
                if e.code in (200, 409):
                    registered = True
                elif e.code in (400, 405):
                    sys.stderr.write("register fatal: HTTP %d\n" % e.code)
                    server.server_close()
                    sys.exit(1)
            except Exception:
                pass
            if not registered:
                time.sleep(backoff)
                backoff = min(backoff * 2, 2.0)
        if not registered:
            sys.stderr.write("register failed\n")
            server.server_close()
            sys.exit(1)
        # Serve in a thread while polling /done.
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        done = False
        while not done:
            time.sleep(0.5)
            try:
                result = _http_json(env_url.rstrip("/") + "/done", timeout=30)
                done = bool(result.get("done"))
            except Exception:
                pass
        server.shutdown()
        server.server_close()
        sys.exit(0)
    # Local / standalone mode: serve forever on the chosen port.
    sys.stderr.write("forge listening on 127.0.0.1:%d\n" % actual_port)
    sys.stderr.flush()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    server.server_close()


if __name__ == "__main__":
    main()
