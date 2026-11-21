-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
-- name    : AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:32:24.37068+00:00
-- url     : https://prove2.me/theorems/879dae1d-6d41-444b-ab8f-13a3e853bce3
-- title:
--   Nonnegative second derivative of explicit one-sided Beta(2,2) Gaussian cap hinge away from the two transition levels
-- statement:
--   For the explicit one-sided Beta(2,2) mollification of the hinge (y-b)^+, and every positive bandwidth ε, the second derivative is nonnegative at any y different from the two transition levels b and b+ε. Below and above the smoothing strip this follows from exact zero curvature, and in the open strip from its explicit formula 6(y-b)(ε-y+b)/ε³. The two exceptional levels are handled by separate zero-Lebesgue-occupation results when applying the original finite-cap stopped Gaussian Ito ledger.
-- source:
--   Combines independently verified original finite-cap one-sided smoothing curvature lemmas into the exact nonnegative curvature fact needed to make the signed dividend cap kink dissipative, without assuming source stochastic Ito.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_nonnegative_curvature_off_transition_levels
    (b ε y : ℝ) (hε : 0 < ε) (hb : y ≠ b) (hu : y ≠ b + ε) :
    let Q : ℝ → ℝ := fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
    0 ≤ iteratedDeriv 2 Q y := by sorry
