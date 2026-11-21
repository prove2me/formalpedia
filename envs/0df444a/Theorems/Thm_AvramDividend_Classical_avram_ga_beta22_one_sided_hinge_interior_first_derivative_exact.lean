-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
-- name    : AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:01:49.58835+00:00
-- url     : https://prove2.me/theorems/6fc6c286-65d3-48ca-a913-24815d57310b
-- title:
--   Exact derivative on interior of explicit one-sided Gaussian cap-kink smoothing strip
-- statement:
--   Let Qε,b be the explicit one-sided Beta(2,2) mollification of the positive hinge (y-b)^+: zero below b, cubic minus quartic on [b,b+ε], affine above. On the open smoothing strip b<y<b+ε, its classical first derivative equals 3(y-b)^2/ε²-2(y-b)^3/ε³. This exact derivative supplies the first step of the true nonpositive weak Gaussian cap-kink smoothing curvature, with no second derivative interchange falsely assumed at the kink.
-- source:
--   Finitecap original stopped Gaussian Ito-Stieltjes source 0ef5d778: exact one-sided explicit smoothing of cap kink, decomposed into small compiler-checkable analytic theorems.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_first_derivative_exact
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    deriv (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y =
      (3 / ε ^ 2) * (y - b) ^ 2 -
        (2 / ε ^ 3) * (y - b) ^ 3 := by sorry
