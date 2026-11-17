-- Prove2me | Theorems.Thm_DirKECC1549_Asm_phi_push
-- name    : DirKECC1549.Asm.phi_push
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T06:12:42.684007+00:00
-- url     : https://prove2.me/theorems/8937a63a-1e44-43d5-920b-617246c358be
-- title:
--   Depth-first search: a push raises the potential by two
-- statement:
--   Advancing the pointer of the top vertex and pushing a new vertex raises $\Phi$ by exactly $2$.
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

theorem DirKECC1549.Asm.phi_push (D : Fin m → Fin n × Fin n) (stk po : List (Fin n)) (ptr : Fin n → ℕ) (v t : Fin n)
    (hv : v ∈ stk) (ht : t ∉ stk) (hlo : ots D v ≤ ptr v) :
    Phi D (stk ++ [t]) po (Function.update (Function.update ptr v (ptr v + 1)) t (ots D t)) =
      Phi D stk po ptr + 2 := by sorry
