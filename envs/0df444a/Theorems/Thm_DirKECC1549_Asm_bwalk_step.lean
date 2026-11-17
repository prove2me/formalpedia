-- Prove2me | Theorems.Thm_DirKECC1549_Asm_bwalk_step
-- name    : DirKECC1549.Asm.bwalk_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-16T07:02:43.971198+00:00
-- url     : https://prove2.me/theorems/cf720fd4-7d04-4362-95d7-365c83da0633
-- title:
--   Residual search: one step back along the parent edges
-- statement:
--   From a queue vertex $q_i$, $i>0$, with a residual trail $t$ to $r$ made of parent edges of later queue vertices, prepending the parent edge of $q_i$ gives such a trail from an earlier queue vertex $q_j$, $j<i$.
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

theorem DirKECC1549.Asm.bwalk_step (H : Fin m → Fin n × Fin n) (z r : Fin n) (q : List (Fin n)) (h : ℕ)
    (par : Fin n → Fin m) (hS : FState H z q h par) (i : ℕ) (hi : i < q.length) (h0 : 0 < i)
    (t : List (Fin m)) (hW : BWalk H q par r i hi t) :
    ∃ j, ∃ hj : j < i, (H (par q[i])).1 = q[j]'(by omega) ∧
      BWalk H q par r j (by omega) (par q[i] :: t) := by sorry
