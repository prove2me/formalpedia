-- Prove2me | Theorems.Thm_BertsekasDP_rollout_sequential_consistency
-- name    : BertsekasDP.rollout_sequential_consistency
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-11T01:22:19.674969+00:00
-- url     : https://prove2.me/theorems/e1c9c478-6b2f-4a06-b22b-5fcefc872805
-- title:
--   Rollout under sequential consistency (Prop. 6.4.1)
-- statement:
--   **Proposition 6.4.1 (termination and improvement under sequential consistency).** Let the base heuristic $\mathcal{H}$ be sequentially consistent, and run the rollout algorithm with the source's tie-breaking convention: when several neighbors attain $\min_{j \in N(i)} H(j)$ and one of them is the successor that $\mathcal{H}$ itself would take from $i$, that one is chosen. Then:
--
--   1. **The rollout terminates:** the run reaches a destination node after finitely many steps.
--   2. **It improves on the base heuristic:** at any time $K$ at which a destination is reached,
--   $$H(i_K) \;\le\; H(i_1), \qquad H(i_K) \;=\; \min\Bigl\{\, H(i_1), \; \min_{j \in N(i_1)} H(j), \; \dots, \; \min_{j \in N(i_{K-1})} H(j) \,\Bigr\}.$$
--
--   The tie-breaking convention is not a technicality: the source exhibits a graph in which, with ties broken the other way, the rollout cycles forever without reaching a destination. Sequential consistency makes the $H$-values along the run non-increasing, and each plateau shortens the base heuristic's remaining path by one arc, which is what forces termination.
--
--   **Formalization Note** The run is modeled as an infinite sequence that obeys the selection rule while at a non-destination node and stays put once at a destination, so "terminates" is the genuine claim that some index lands in the destination set, rather than an assumption built into the shape of the object. The cost claim is stated for every such index. As in Prop. 6.4.2, the minimum is phrased as a least element, asserting attainment as well as the bound.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 6.4.1

import Mathlib
import Definitions.Def_BertsekasGraphSearch

namespace BertsekasDP

theorem rollout_sequential_consistency {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasGraphSearch V) (H : BertsekasBaseHeuristic G)
    (hcons : BertsekasSeqConsistent G H)
    (r : ℕ → V) (hstart : r 0 ∉ G.dest)
    (hstep : ∀ k, r k ∉ G.dest →
      r (k + 1) ∈ BertsekasNbrs G (r k) ∧
      (∀ j ∈ BertsekasNbrs G (r k),
        BertsekasHeurCost G H (r (k + 1)) ≤ BertsekasHeurCost G H j))
    (htie : ∀ k, r k ∉ G.dest → ∀ (jH : V) (l : List V),
      H.path (r k) = r k :: jH :: l →
      (∀ j ∈ BertsekasNbrs G (r k),
        BertsekasHeurCost G H jH ≤ BertsekasHeurCost G H j) →
      r (k + 1) = jH)
    (habsorb : ∀ k, r k ∈ G.dest → r (k + 1) = r k) :
    (∃ K, r K ∈ G.dest) ∧
    (∀ K, r K ∈ G.dest →
      BertsekasHeurCost G H (r K) ≤ BertsekasHeurCost G H (r 0) ∧
      IsLeast {c : ℝ | c = BertsekasHeurCost G H (r 0) ∨
          ∃ k < K, r k ∉ G.dest ∧
            ∃ j ∈ BertsekasNbrs G (r k), c = BertsekasHeurCost G H j}
        (BertsekasHeurCost G H (r K))) := by sorry

end BertsekasDP
