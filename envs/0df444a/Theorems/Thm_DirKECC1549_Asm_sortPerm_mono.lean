-- Prove2me | Theorems.Thm_DirKECC1549_Asm_sortPerm_mono
-- name    : DirKECC1549.Asm.sortPerm_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T03:59:34.347299+00:00
-- url     : https://prove2.me/theorems/ee13f272-94e9-483f-b93a-00c95f17fd35
-- title:
--   The counting-sort permutation sorts by key
-- statement:
--   The permutation $\sigma$ with $\sigma(\mathrm{pos}(e))=e$ (which exists because $\mathrm{pos}$ is injective with values below $m$) is monotone in the key: $i\le j$ implies $\kappa(\sigma(i))\le\kappa(\sigma(j))$.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the graph layout (the child contract `graph_layout_impl`): from the edge list of a multigraph with $n$ vertices and $m$ edges the program builds, by two stable counting sorts (by tail and by head), the start offsets $\#\{e: \mathrm{tail}(e)<v\}$ and the edge ids sorted by tail, and the same for heads, in $O(m+n)$ time, restoring the input cells it uses as registers. A counting sort of keys $\kappa(e)<n$ places edge $e$ at position $\mathrm{pos}(e)=\#\{e':\kappa(e')<\kappa(e)\}+\#\{e'<e:\kappa(e')=\kappa(e)\}$.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_LayComb

set_option autoImplicit false
open Classical Finset
open DirKECC1549 DirKECC1549.Asm
variable {m : ℕ}

theorem DirKECC1549.Asm.sortPerm_mono (key : Fin m → ℕ) : Monotone (fun i => key (sortPerm key i)) := by sorry
