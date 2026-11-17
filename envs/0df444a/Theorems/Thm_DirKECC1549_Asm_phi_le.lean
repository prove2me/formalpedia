-- Prove2me | Theorems.Thm_DirKECC1549_Asm_phi_le
-- name    : DirKECC1549.Asm.phi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:15.404873+00:00
-- url     : https://prove2.me/theorems/d81c954f-a7f0-4853-8f7c-1d6feccc53cf
-- title:
--   Depth-first search: the potential is bounded
-- statement:
--   The potential $\Phi$ (twice the finished vertices plus stack vertices plus scanned out-edges) of any search state is at most $2n+m$.
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

theorem DirKECC1549.Asm.phi_le (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (stk po : List (Fin n))
    (ptr : Fin n → ℕ) (h : DState D σ stk po ptr) : Phi D stk po ptr ≤ 2 * n + m := by sorry
