-- Prove2me | Theorems.Thm_DirKECC1549_Asm_fstate_visit
-- name    : DirKECC1549.Asm.fstate_visit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T07:02:16.756192+00:00
-- url     : https://prove2.me/theorems/8a969ef4-23c3-48f7-aa8b-272c247c9566
-- title:
--   Residual search: visiting a new vertex
-- statement:
--   Appending the head $y\notin q$ of a residual edge $e$ out of the current queue vertex $q_h$, with parent edge $e$, keeps the search state `FState` (queue without repetitions starting at $z$, parent edges from earlier queue vertices, processed vertices closed).
--
--   **Context.** This lemma belongs to the machine-checked word-RAM implementation of Lemma 3 of the paper (Ford–Fulkerson with at most $k$ augmentations, the platform theorem `lemma_3_flow`): starting from the empty flow, each round runs a breadth-first search from $z$ in the residual graph (flow edges reversed, scanned through the out-adjacency array for edges without flow and the in-adjacency array for edges with flow); if $r$ is reached, the flow bits along the parent trail from $r$ back to $z$ are toggled, otherwise the visited set is a cut of the current flow value. After at most $k$ rounds the program outputs $q=\min\{k,\lambda(z,r)\}$ and the residual graph, in $O(k(m+n))$ ticks.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model of Hagerup (p.25). Implementation-level lemma of the verified program for Lemma 5.

import Definitions.Def_DirKECC1549_Impl_FlowBfs

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem DirKECC1549.Asm.fstate_visit (H : Fin m → Fin n × Fin n) (z : Fin n) (q : List (Fin n)) (h : ℕ)
    (par : Fin n → Fin m) (hS : FState H z q h par) (hh : h < q.length) (e : Fin m)
    (he1 : (H e).1 = q[h]) (hy : (H e).2 ∉ q) :
    FState H z (q ++ [(H e).2]) h (Function.update par (H e).2 e) := by sorry
