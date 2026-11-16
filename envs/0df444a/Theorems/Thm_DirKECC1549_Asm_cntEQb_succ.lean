-- Prove2me | Theorems.Thm_DirKECC1549_Asm_cntEQb_succ
-- name    : DirKECC1549.Asm.cntEQb_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T03:52:05.899306+00:00
-- url     : https://prove2.me/theorems/01efcbd3-97a9-4688-be69-e829039cf2b3
-- title:
--   Counting the edges with a given key among the first $j+1$
-- statement:
--   For $j<m$, the number of edges $e<j+1$ with key $v$ equals the number of edges $e<j$ with key $v$, plus $1$ if edge $j$ has key $v$.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the graph layout (the child contract `graph_layout_impl`): from the edge list of a multigraph with $n$ vertices and $m$ edges the program builds, by two stable counting sorts (by tail and by head), the start offsets $\#\{e: \mathrm{tail}(e)<v\}$ and the edge ids sorted by tail, and the same for heads, in $O(m+n)$ time, restoring the input cells it uses as registers. A counting sort of keys $\kappa(e)<n$ places edge $e$ at position $\mathrm{pos}(e)=\#\{e':\kappa(e')<\kappa(e)\}+\#\{e'<e:\kappa(e')=\kappa(e)\}$.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_LayComb

set_option autoImplicit false
open Classical Finset
open DirKECC1549 DirKECC1549.Asm
variable {m : ℕ}

theorem DirKECC1549.Asm.cntEQb_succ (key : Fin m → ℕ) (j : ℕ) (hj : j < m) (v : ℕ) :
    cntEQb key (j + 1) v = cntEQb key j v + if key ⟨j, hj⟩ = v then 1 else 0 := by sorry
