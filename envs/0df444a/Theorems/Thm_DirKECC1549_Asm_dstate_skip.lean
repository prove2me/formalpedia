-- Prove2me | Theorems.Thm_DirKECC1549_Asm_dstate_skip
-- name    : DirKECC1549.Asm.dstate_skip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:08.466238+00:00
-- url     : https://prove2.me/theorems/0a5616a6-d8bd-421e-a081-7ffbf6c5d071
-- title:
--   Depth-first search: skipping a visited head
-- statement:
--   If the next out-edge of the top vertex leads to a vertex on the stack or already finished, advancing the pointer keeps `DState`.
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

theorem DirKECC1549.Asm.dstate_skip (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (stk po : List (Fin n))
    (v : Fin n) (hv : v ∈ stk) (ptr : Fin n → ℕ) (h : DState D σ stk po ptr) (i : Fin m)
    (hi : (i : ℕ) = ptr v) (hp : ptr v < ots D (v + 1))
    (ht : (D (σ i)).2 ∈ stk ∨ (D (σ i)).2 ∈ po) :
    DState D σ stk po (Function.update ptr v (ptr v + 1)) := by sorry
