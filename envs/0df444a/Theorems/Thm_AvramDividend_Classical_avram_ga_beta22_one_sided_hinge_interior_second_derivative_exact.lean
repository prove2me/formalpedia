-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
-- name    : AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:29:09.751164+00:00
-- url     : https://prove2.me/theorems/25610f44-6269-4296-b1d1-1ec468074644
-- title:
--   Exact second derivative of one-sided Beta(2,2) Gaussian cap smoothing in its open transition strip
-- statement:
--   On the strip b<y<b+ε, the second classical derivative of the explicit one-sided Beta(2,2) convolution of (y-b)^+ equals 6(y-b)/ε²-6(y-b)²/ε³. Derive this from the already Proved first derivative theorem, local equality on an open interval, and polynomial HasDerivAt rules. This is the independent analytic Hessian identity for the genuinely favourable signed upper-cap kink correction.
-- source:
--   Separates the exact second-derivative computation from its sign, reducing the original finite-cap Gaussian Ito smoothing source to independently verified reusable calculus facts.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_interior_second_derivative_exact
    (b ε y : ℝ) (hε : 0 < ε) (hy : b < y) (hu : y < b + ε) :
    iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y =
      (6 / ε ^ 2) * (y - b) - (6 / ε ^ 3) * (y - b) ^ 2 := by sorry
