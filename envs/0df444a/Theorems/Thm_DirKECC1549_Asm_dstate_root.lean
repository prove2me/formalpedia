-- Prove2me | Theorems.Thm_DirKECC1549_Asm_dstate_root
-- name    : DirKECC1549.Asm.dstate_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:20.35224+00:00
-- url     : https://prove2.me/theorems/7454c0c6-9a15-4b5b-b52d-d40ee7c8b178
-- title:
--   Depth-first search: starting a new root
-- statement:
--   For an empty stack and an unfinished vertex $s$, pushing $s$ with its out-pointer at the start of its out-edge block keeps the search state `DState`.
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

theorem DirKECC1549.Asm.dstate_root (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (po : List (Fin n))
    (ptr : Fin n → ℕ) (h : DState D σ [] po ptr) (s : Fin n) (hs : s ∉ po) :
    DState D σ [s] po (Function.update ptr s (ots D s)) := by sorry
