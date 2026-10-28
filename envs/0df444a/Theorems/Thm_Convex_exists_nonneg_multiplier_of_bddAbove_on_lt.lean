-- Prove2me | Theorems.Thm_Convex_exists_nonneg_multiplier_of_bddAbove_on_lt
-- name    : Convex.exists_nonneg_multiplier_of_bddAbove_on_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:29.041251+00:00
-- url     : https://prove2.me/theorems/840d9eff-45da-4ed8-a18f-51286f0aaf31
-- title:
--   A supporting multiplier for a planar convex set bounded above on a half-plane
-- statement:
--   Let $C \subseteq \mathbb{R}^2$ be convex. Write a point of $C$ as $(t, v)$, thinking of $t$ as a
--   cost and $v$ as a value. Fix $\delta \in \mathbb{R}$ and suppose
--
--   1. $C$ reaches strictly below the threshold: $(c_0, L) \in C$ for some $c_0 < \delta$ and
--      $L \in \mathbb{R}$;
--   2. the value is bounded by $V$ wherever the cost is strictly below the threshold:
--      $v \le V$ for every $(t, v) \in C$ with $t < \delta$.
--
--   Then one nonnegative multiplier extends that bound to all of $C$:
--
--   $$
--   \exists\, \gamma \ge 0 \ \text{ such that } \ v \le V + \gamma\,(t - \delta) \quad
--   \text{for every } (t, v) \in C .
--   $$
--
--   This is Lagrangian duality in its smallest nontrivial case, and the shape in which a budget
--   constraint is traded for a price. The bound is assumed only on the open half-plane $t < \delta$
--   and the conclusion holds everywhere, including at and beyond the threshold, where the
--   multiplier pays for the excess cost. Condition 1 is the Slater point; without it the conclusion
--   can fail.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 422-497, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem Convex.exists_nonneg_multiplier_of_bddAbove_on_lt (C : Set (ℝ × ℝ)) (hC : Convex ℝ C)
    (δ V c0 L : ℝ) (hδ : c0 < δ) (hbase : (c0, L) ∈ C)
    (hbudget : ∀ z ∈ C, z.1 < δ → z.2 ≤ V) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z ∈ C, z.2 ≤ V + γ * (z.1 - δ) := by sorry
