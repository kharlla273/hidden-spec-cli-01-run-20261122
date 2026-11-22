// main.ts is mend, the CLI SPEC.md specifies: one patch tool for every AI edit format.
// It reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks, V4A, JSON
// edits), finds each edit's lines at the first of three matching tiers, and writes every
// change or none, printing what it changed or why it failed. Node 22, standard library
// alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this
// file hands over to runner.ts (the last lines below): keep that hand-over and runner.ts
// as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its own break, its lines, and whether it ended with a break. */
interface FileModel {
  lines: string[];
  br: string;
  finalBr: boolean;
}

function splitFile(text: string): FileModel {
  if (text === '') return { lines: [], br: '\n', finalBr: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBr = text.endsWith(br);
  if (finalBr) parts.pop();
  return { lines: parts, br, finalBr };
}

function joinFile(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.br) + (m.finalBr ? m.br : '');
}

const leadOf = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};
const rtrimWs = (s: string): string => s.replace(/[ \t]+$/, '');
const trimWs = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

/** Whether one line matches another at a tier (section 5). */
function lineMatches(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimWs(a) === rtrimWs(b);
  return trimWs(a) === trimWs(b);
}

function tiersToTry(strict: boolean): number[] {
  return strict ? [0] : [0, 1, 2];
}

/** Positions at or after `from` where O occurs in F at one tier. */
function occurrencesAt(O: string[], F: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (O.length === 0) return out;
  for (let i = Math.max(0, from); i + O.length <= F.length; i++) {
    let ok = true;
    for (let j = 0; j < O.length; j++) {
      if (!lineMatches(O[j]!, F[i + j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs in F at or after `from`, with its positions. */
function findTier(O: string[], F: string[], strict: boolean, from: number): { tier: number; positions: number[] } | null {
  for (const t of tiersToTry(strict)) {
    const positions = occurrencesAt(O, F, t, from);
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

/** Re-indent one new line at tier 2 (section 5): P replaced by F when it leads the line. */
function reindentLine(line: string, fLead: string, pLead: string): string {
  if (line === '' || line.trim() === '') return line;
  if (!line.startsWith(pLead)) return line;
  return fLead + line.slice(pLead.length);
}

/** One line of N: a context line (taken from the file) or a fresh line. */
interface NLine {
  text: string;
  ctx: boolean;
  oIdx: number;
}

/** Map N onto the file at a match: context lines come from the file, the rest are
 *  re-indented at tier 2 and written as they are at tiers 0 and 1. */
function mapNewLines(nLines: NLine[], fileLines: string[], pos: number, tier: number, oFirst: string): string[] {
  if (tier !== 2) return nLines.map((n) => (n.ctx ? fileLines[pos + n.oIdx]! : n.text));
  const fLead = leadOf(fileLines[pos] ?? '');
  const pLead = leadOf(oFirst);
  return nLines.map((n) => (n.ctx ? fileLines[pos + n.oIdx]! : reindentLine(n.text, fLead, pLead)));
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<{ old: string; nw: string }> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  recordMove(oldP: string, newP: string): void {
    this.moves.push({ old: oldP, nw: newP });
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/* ---- Unified diffs (SPEC.md section 6) ---- */

interface Hunk {
  a: number;
  body: string[];
  o: string[];
  n: NLine[];
  noNl: boolean;
  lastPlus: number;
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hasPair: boolean;
  hunks: Hunk[];
}

/** The path a `--- ` or `+++ ` header line names, or null for /dev/null. */
function headerPath(line: string): string | null {
  const raw = line.slice(4).split('\t')[0]!.trim();
  if (raw === '/dev/null') return null;
  if (raw.startsWith('a/') || raw.startsWith('b/')) return raw.slice(2);
  return raw;
}

/** Split a hunk body into its old lines O and its new lines N. */
function buildHunk(a: number, body: string[]): Hunk {
  const o: string[] = [];
  const n: NLine[] = [];
  let lastCtxPlus = -1;
  let lastPlus = -1;
  for (let k = 0; k < body.length; k++) {
    const bl = body[k]!;
    if (bl === '' || bl.startsWith(' ') || bl.startsWith('+')) lastCtxPlus = k;
    if (bl.startsWith('+')) lastPlus = k;
  }
  const noNl = lastCtxPlus >= 0 && lastCtxPlus + 1 < body.length && body[lastCtxPlus + 1]!.startsWith('\\');
  for (const bl of body) {
    if (bl === '' || bl.startsWith(' ')) {
      const t = bl === '' ? '' : bl.slice(1);
      o.push(t);
      n.push({ text: t, ctx: true, oIdx: o.length - 1 });
    } else if (bl.startsWith('-')) {
      o.push(bl.slice(1));
    } else if (bl.startsWith('+')) {
      n.push({ text: bl.slice(1), ctx: false, oIdx: -1 });
    }
  }
  return { a, body, o, n, noNl, lastPlus };
}

/** Apply one hunk to a file model; `d` is the line drift of this section's earlier hunks. */
function applyUnifiedHunk(model: FileModel, hk: Hunk, d: number, strict: boolean, path: string): FileModel {
  const F = model.lines;
  if (hk.o.length === 0) {
    const pos = Math.max(0, Math.min(hk.a + d, F.length));
    const ins = hk.n.map((nl) => nl.text);
    const lines = [...F.slice(0, pos), ...ins, ...F.slice(pos)];
    return { lines, br: model.br, finalBr: pos === F.length ? !hk.noNl : model.finalBr };
  }
  const found = findTier(hk.o, F, strict, 0);
  if (found === null) throw new Fail('no-match', path);
  const target = hk.a - 1 + d;
  let best = found.positions[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.positions) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const mapped = mapNewLines(hk.n, F, best, found.tier, hk.o[0]!);
  const lines = [...F.slice(0, best), ...mapped, ...F.slice(best + hk.o.length)];
  return { lines, br: model.br, finalBr: best + hk.o.length === F.length ? !hk.noNl : model.finalBr };
}

/** One unified section as an edit. */
function unifiedEdit(sec: Section, strict: boolean): Edit {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    const isCreate = oldP === null || sec.newFile;
    if (isCreate) {
      if (newP === null) throw new Fail('unsafe', '/dev/null');
      if (!safe(newP)) throw new Fail('unsafe', newP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const plus: string[] = [];
      for (const hk of sec.hunks) for (const nl of hk.n) if (!nl.ctx) plus.push(nl.text);
      let noNl = false;
      for (let h = sec.hunks.length - 1; h >= 0; h--) {
        const hk = sec.hunks[h]!;
        if (hk.lastPlus >= 0) {
          noNl = hk.lastPlus + 1 < hk.body.length && hk.body[hk.lastPlus + 1]!.startsWith('\\');
          break;
        }
      }
      tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noNl ? '' : '\n'));
      return;
    }
    const isDelete = newP === null || sec.deletedFile;
    if (isDelete) {
      if (oldP === null) throw new Fail('unsafe', '/dev/null');
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, null);
      return;
    }
    const isMove = oldP !== null && newP !== null && oldP !== newP;
    if (oldP === null) throw new Fail('unsafe', '/dev/null');
    if (!safe(oldP)) throw new Fail('unsafe', oldP);
    if (isMove) {
      if (newP === null) throw new Fail('unsafe', '/dev/null');
      if (!safe(newP!)) throw new Fail('unsafe', newP!);
    }
    const cur = tree.get(oldP);
    if (cur === null) throw new Fail('missing', oldP);
    if (isMove && tree.get(newP!) !== null) throw new Fail('exists', newP!);
    let model = splitFile(cur);
    let d = 0;
    for (const hk of sec.hunks) {
      model = applyUnifiedHunk(model, hk, d, strict, oldP);
      d += hk.n.length - hk.o.length;
    }
    const text = joinFile(model);
    if (isMove) {
      tree.now.set(oldP, null);
      tree.now.set(newP!, text);
      tree.recordMove(oldP, newP!);
    } else {
      tree.now.set(oldP, text);
    }
  };
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  const diffRe = /^diff --git a\/(\S+) b\/(\S+)\s*$/;
  const hunkRe = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;
  let cur: Section | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = diffRe.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: m[1]!, newPath: m[2]!, newFile: false, deletedFile: false, hasPair: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const op = headerPath(line);
      const np = headerPath(lines[i + 1]!);
      if (cur !== null && inHeader && !cur.hasPair) {
        cur.oldPath = op;
        cur.newPath = np;
        cur.hasPair = true;
      } else {
        cur = { oldPath: op, newPath: np, newFile: false, deletedFile: false, hasPair: true, hunks: [] };
        sections.push(cur);
        inHeader = true;
      }
      i += 2;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('--- ')) {
      throw new Exit2(`error: parse ${i + 2}`);
    }
    if (line.startsWith('@@')) {
      const m = hunkRe.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const body: string[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bl);
          j++;
        } else break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      cur.hunks.push(buildHunk(parseInt(m[1]!, 10), body));
      inHeader = false;
      i = j;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ') && !cur.hasPair) cur.oldPath = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ') && !cur.hasPair) cur.newPath = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.deletedFile = true;
      i++;
      continue;
    }
    i++;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedEdit(s, strict));
}

/* ---- SEARCH/REPLACE blocks (SPEC.md section 7) ---- */

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function srEdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(b.path);
    if (cur === null) throw new Fail('missing', b.path);
    const model = splitFile(cur);
    const found = findTier(b.oldLines, model.lines, strict, 0);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.positions.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.positions[0]!;
    const nLines: NLine[] = b.newLines.map((t) => ({ text: t, ctx: false, oIdx: -1 }));
    const mapped = mapNewLines(nLines, model.lines, pos, found.tier, b.oldLines[0]!);
    const lines = [...model.lines.slice(0, pos), ...mapped, ...model.lines.slice(pos + b.oldLines.length)];
    tree.now.set(b.path, joinFile({ lines, br: model.br, finalBr: model.finalBr }));
  };
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const blocks: SRBlock[] = [];
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchNo = i + 1;
    let path: string | null = null;
    for (let j = i - 1; j >= prevEnd; j--) {
      const cand = lines[j]!;
      if (blank(cand)) continue;
      if (cand.trim().startsWith('```')) continue;
      path = cand.trim();
      break;
    }
    if (path === null) {
      if (blocks.length === 0) throw new Exit2(`error: parse ${searchNo}`);
      path = blocks[blocks.length - 1]!.path;
    }
    let eq = -1;
    for (let k = i + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '=======') {
        eq = k;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchNo}`);
    let rep = -1;
    for (let k = eq + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = k;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchNo}`);
    blocks.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevEnd = rep + 1;
    i = rep + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => srEdit(b, strict));
}

/* ---- V4A patches (SPEC.md section 8) ---- */

interface VChunk {
  anchor: string | null;
  o: string[];
  n: NLine[];
  eof: boolean;
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  addLines: string[];
  chunks: VChunk[];
  lineNo: number;
}

interface VRawSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  lineNo: number;
  raw: Array<{ text: string; no: number }>;
}

/** Validate one V4A section's lines eagerly, so a bad section is a parse error. */
function parseV4ASection(s: VRawSection): VSection {
  const raw = [...s.raw];
  while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
  if (s.kind === 'add') {
    const addLines: string[] = [];
    for (const r of raw) {
      if (r.text.startsWith('+')) addLines.push(r.text.slice(1));
      else if (r.text === '') addLines.push('');
      else throw new Exit2(`error: parse ${r.no}`);
    }
    return { kind: 'add', path: s.path, moveTo: null, addLines, chunks: [], lineNo: s.lineNo };
  }
  if (s.kind === 'delete') {
    if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.no}`);
    return { kind: 'delete', path: s.path, moveTo: null, addLines: [], chunks: [], lineNo: s.lineNo };
  }
  let moveTo: string | null = null;
  let idx = 0;
  if (raw.length > 0 && raw[0]!.text.startsWith('*** Move to: ')) {
    moveTo = raw[0]!.text.slice('*** Move to: '.length).trim();
    idx = 1;
  }
  const chunks: VChunk[] = [];
  let curChunk: VChunk | null = null;
  for (let k = idx; k < raw.length; k++) {
    const r = raw[k]!;
    const t = r.text;
    if (t.startsWith('@@')) {
      const anchor = t.slice(2).trim();
      curChunk = { anchor: anchor === '' ? null : anchor, o: [], n: [], eof: false };
      chunks.push(curChunk);
      continue;
    }
    if (t.trim() === '*** End of File') {
      if (curChunk === null) throw new Exit2(`error: parse ${r.no}`);
      curChunk.eof = true;
      curChunk = null;
      continue;
    }
    if (t.startsWith('*** Move to: ')) throw new Exit2(`error: parse ${r.no}`);
    if (t === '' || t.startsWith(' ') || t.startsWith('-') || t.startsWith('+')) {
      if (curChunk === null) {
        if (chunks.length === 0) {
          curChunk = { anchor: null, o: [], n: [], eof: false };
          chunks.push(curChunk);
        } else throw new Exit2(`error: parse ${r.no}`);
      }
      if (t === '' || t.startsWith(' ')) {
        const tx = t === '' ? '' : t.slice(1);
        curChunk.o.push(tx);
        curChunk.n.push({ text: tx, ctx: true, oIdx: curChunk.o.length - 1 });
      } else if (t.startsWith('-')) {
        curChunk.o.push(t.slice(1));
      } else {
        curChunk.n.push({ text: t.slice(1), ctx: false, oIdx: -1 });
      }
      continue;
    }
    throw new Exit2(`error: parse ${r.no}`);
  }
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${s.lineNo}`);
  return { kind: 'update', path: s.path, moveTo, addLines: [], chunks, lineNo: s.lineNo };
}

function v4aEdit(sec: VSection, strict: boolean): Edit {
  return (tree) => {
    if (sec.kind === 'add') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) !== null) throw new Fail('exists', sec.path);
      tree.now.set(sec.path, sec.addLines.length === 0 ? '' : sec.addLines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'delete') {
      if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
      if (tree.get(sec.path) === null) throw new Fail('missing', sec.path);
      tree.now.set(sec.path, null);
      return;
    }
    if (!safe(sec.path)) throw new Fail('unsafe', sec.path);
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const cur = tree.get(sec.path);
    if (cur === null) throw new Fail('missing', sec.path);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    let model = splitFile(cur);
    let cursor = 0;
    for (const ch of sec.chunks) {
      if (ch.anchor !== null) {
        const single = findTier([ch.anchor], model.lines, strict, cursor);
        if (single === null) throw new Fail('no-match', sec.path);
        cursor = single.positions[0]! + 1;
      }
      if (ch.o.length === 0) {
        const pos = ch.eof ? model.lines.length : cursor;
        const ins = ch.n.map((nl) => nl.text);
        model = { lines: [...model.lines.slice(0, pos), ...ins, ...model.lines.slice(pos)], br: model.br, finalBr: model.finalBr };
        cursor = pos + ins.length;
        continue;
      }
      let found: { tier: number; pos: number } | null = null;
      for (const t of tiersToTry(strict)) {
        const occ = occurrencesAt(ch.o, model.lines, t, cursor).filter((p) => !ch.eof || p + ch.o.length === model.lines.length);
        if (occ.length > 0) {
          found = { tier: t, pos: occ[0]! };
          break;
        }
      }
      if (found === null) throw new Fail('no-match', sec.path);
      const mapped = mapNewLines(ch.n, model.lines, found.pos, found.tier, ch.o[0]!);
      const lines = [...model.lines.slice(0, found.pos), ...mapped, ...model.lines.slice(found.pos + ch.o.length)];
      model = { lines, br: model.br, finalBr: model.finalBr };
      cursor = found.pos + mapped.length;
    }
    const text = joinFile(model);
    if (sec.moveTo !== null) {
      tree.now.set(sec.path, null);
      tree.now.set(sec.moveTo, text);
      tree.recordMove(sec.path, sec.moveTo);
    } else {
      tree.now.set(sec.path, text);
    }
  };
}

function parseV4A(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const rawSections: VRawSection[] = [];
  let curSec: VRawSection | null = null;
  for (let k = first + 1; k < last; k++) {
    const line = lines[k]!;
    const isAdd = line.startsWith('*** Add File: ');
    const isDel = line.startsWith('*** Delete File: ');
    const isUpd = line.startsWith('*** Update File: ');
    if (isAdd || isDel || isUpd) {
      const kind = isAdd ? 'add' : isDel ? 'delete' : 'update';
      const prefix = isAdd ? '*** Add File: '.length : isDel ? '*** Delete File: '.length : '*** Update File: '.length;
      curSec = { kind, path: line.slice(prefix).trim(), lineNo: k + 1, raw: [] };
      rawSections.push(curSec);
      continue;
    }
    if (curSec === null) {
      if (blank(line)) continue;
      throw new Exit2(`error: parse ${k + 1}`);
    }
    curSec.raw.push({ text: line, no: k + 1 });
  }
  if (rawSections.length === 0) throw new Exit2('error: parse 1');
  return rawSections.map((s) => v4aEdit(parseV4ASection(s), strict));
}

/* ---- JSON edits (SPEC.md section 9) ---- */

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* ---- Entry point (sections 1, 2 and 10) ---- */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4A(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // Output rows: a successful move collapses its D/A pair into one R line, sorted by <new>.
  interface Row {
    key: string;
    text: string;
  }
  const rows: Row[] = [];
  const covered = new Set<string>();
  for (const mv of tree.moves) {
    const wasOld = tree.original(mv.old);
    const wasNew = tree.original(mv.nw);
    if (wasOld !== null && wasNew === null && tree.get(mv.old) === null && tree.get(mv.nw) !== null) {
      rows.push({ key: mv.nw, text: `R ${mv.old} -> ${mv.nw}` });
      covered.add(mv.old);
      covered.add(mv.nw);
    }
  }
  for (const p of [...tree.now.keys()]) {
    if (covered.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outLines = rows.map((r) => r.text);
  if (!check) {
    const dels = [...tree.now.keys()].filter((p) => tree.now.get(p) === null && tree.original(p) !== null);
    dels.sort((a, b) => b.split('/').length - a.split('/').length || Buffer.compare(Buffer.from(b), Buffer.from(a)));
    for (const p of dels) rmSync(p, { force: true });
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const now = tree.now.get(p)!;
      if (now === null) continue;
      if (tree.original(p) === now) continue;
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
