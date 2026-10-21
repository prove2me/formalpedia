-- Prove2me | Theorems.Thm_FlowsNetworks_TwoArcs_eq_13_1_max_flow_min_cut
-- name    : FlowsNetworks.TwoArcs.eq_13_1_max_flow_min_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:07.164495+00:00
-- url     : https://prove2.me/theorems/c5a253b4-a588-4d94-8d56-00c0e81cc129
-- title:
--   Chapter I, Eq. (13.1) — the maximal flow value from S to T is the minimal capacity of a cut separating S and T
-- statement:
--   Let $[N;\mathcal A]$ be a network with a set $S$ of sources and a disjoint set $T$ of sinks, and let every arc carry a finite capacity $c(x,y)\ge0$. Let $\bar v$ be the maximal flow value from $S$ to $T$. Then $\bar v$ is the least capacity of a cut separating $S$ and $T$:
--
--   $$\bar v = \min_{X:\ S\subseteq X,\ T\cap X=\emptyset} c(X,\bar X),$$
--
--   and the minimum is attained.
--
--   This is the max-flow min-cut theorem for several sources and sinks; in Section 13 of Ford and Fulkerson it is the starting point for studying $\bar v$ as a function of individual arc capacities.
--
--   **Formalization Note** Stated as `IsLeast` of the set of cut capacities (indexed by node sets $X$ containing every source and no sink) at the maximal flow value, both in `ℝ≥0∞`. The set is nonempty because $X=S$ is admissible.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, pp. 52–53, Eq. (13.1)

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

/-- Ch. I, §13, Eq. (13.1), p. 52: for a network with sources `S`, sinks `T` and finite
nonnegative arc capacities `c`, the maximal flow value from `S` to `T` is the minimum, over the
cuts `(X, X̄)` separating `S` and `T`, of the cut capacity `c(X, X̄)`. -/
theorem eq_13_1_max_flow_min_cut {N : Type} [Fintype N] [DecidableEq N]
    (G : Network N) (c : N × N → ℝ≥0) :
    IsLeast {r : ℝ≥0∞ | ∃ X : Finset N, IsSeparating G X ∧
        r = cutCapacity G (fun a => (c a : ℝ≥0∞)) X}
      (maxFlowValue G (fun a => (c a : ℝ≥0∞))) := by sorry

end FlowsNetworks.TwoArcs
