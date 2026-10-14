-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_profitable_deviation_cycle
-- name    : FlowAllocGames.StrongEq.profitable_deviation_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:21.098683+00:00
-- url     : https://prove2.me/theorems/9010d5ea-4842-4156-bb7f-7093a812fe35
-- title:
--   Proof of Theorem 9, pp. 23–24 — a profitable coalitional deviation yields a cycle of edges with strictly more flow
-- statement:
--   Let $\mathbf a$ be a unit-ranking profile of a flow allocation game with clearing state $\hat{\mathbf f}$. Suppose a non-empty coalition $C \subseteq V$ has a profitable deviation $\mathbf a'_C$: the profile $(\mathbf a'_C, \mathbf a_{-C})$ is unit-ranking, and with its clearing state $\hat{\mathbf f}'$ every member is strictly better off,
--
--   $$u_v(\mathbf a'_C, \mathbf a_{-C}) > u_v(\mathbf a) \qquad \text{for every } v \in C.$$
--
--   Then there is a cycle in $G$ — a non-empty closed walk $e_1, e_2, \dots, e_k$ of pairwise distinct edges with $\mathrm{head}(e_i) = \mathrm{tail}(e_{i+1})$ and $\mathrm{head}(e_k) = \mathrm{tail}(e_1)$ — all of whose edges carry strictly more flow after the deviation:
--
--   $$\hat f'_{e_i} > \hat f_{e_i} \qquad (i = 1, \dots, k).$$
--
--   In the proof of Theorem 9 this is applied to $\mathbf a = \mathbf a^*$, whose clearing state is the optimal circulation $f^*$; the cycle could be used to increase $f^*$, a contradiction, so $\mathbf a^*$ is a strong equilibrium.
--
--   **Formalization Note.** The page argues for the specific profile $\mathbf a^*$; the argument only uses that $\mathbf a^*$ is unit-ranking, and is stated here for an arbitrary unit-ranking profile (a generalization). The cycle is a list of edges without repetition; a self-loop is a cycle of length one. The coalition is non-empty, as in the definition of strong equilibrium.
-- source:
--   arXiv:1908.01714v3, proof of Theorem 9, p. 23 (last paragraph) to p. 24 (first two paragraphs)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

/-- Proof of Theorem 9 (arXiv:1908.01714v3, pp. 23–24), stated for an arbitrary unit-ranking
profile `a`: if a non-empty coalition `C` has a profitable unit-ranking deviation from `a`, there is
a non-empty closed walk of distinct edges of `G` on each of which the clearing state of the new
profile carries strictly more flow than the clearing state of `a`. -/
theorem profitable_deviation_cycle {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) (a : Profile E) (ha : G.IsUnitRanking a)
    (C : Finset V) (hC : C.Nonempty) (a' : Profile E) (ha' : G.IsUnitRanking (G.deviate a a' C))
    (hprof : ∀ v ∈ C, G.utility a v < G.utility (G.deviate a a' C) v) :
    ∃ cyc : List E, cyc ≠ [] ∧ cyc.Nodup ∧ cyc.IsChain (fun e e' => G.head e = G.tail e') ∧
      (∀ h : cyc ≠ [], G.head (cyc.getLast h) = G.tail (cyc.head h)) ∧
      ∀ e ∈ cyc, G.clearingState a e < G.clearingState (G.deviate a a' C) e := by sorry

end FlowAllocGames.StrongEq
