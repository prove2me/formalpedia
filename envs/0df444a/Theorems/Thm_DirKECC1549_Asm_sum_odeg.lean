-- Prove2me | Theorems.Thm_DirKECC1549_Asm_sum_odeg
-- name    : DirKECC1549.Asm.sum_odeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T07:02:20.870417+00:00
-- url     : https://prove2.me/theorems/713d4ff3-5f5c-4e1b-ad93-7bbd325ebf7d
-- title:
--   Out-degrees sum to at most m
-- statement:
--   For any set $S$ of vertices, $\sum_{v\in S}\mathrm{outdeg}(v)\le m$, where $\mathrm{outdeg}(v)=\mathrm{ots}(v+1)-\mathrm{ots}(v)$ is read from the sorted out-adjacency block starts.
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of the strongly connected components computation used by Algorithm 3 (the child contract `scc_impl`): Kosaraju's algorithm with an iterative depth-first search on $D$ producing the post-order (pass 1), followed by searches on reversed edges from the vertices in decreasing post-order, each labelling one component (pass 2), all in $O(n+m)$ ticks on the graph layout.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.sum_odeg (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) : ∑ v ∈ S, odeg D v ≤ m := by sorry
