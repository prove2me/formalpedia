-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
-- name    : AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:05:13.158305+00:00
-- url     : https://prove2.me/theorems/42c19103-d19f-47ff-9881-f3d0fef6cd55
-- title:
--   One-sided Beta(2,2) smoothed Gaussian cap-kink has zero second derivative off its support strip
-- statement:
--   For the explicit one-sided Beta(2,2) mollification of the positive hinge (y-b)^+, show its second derivative vanishes at every y strictly below b or strictly above b+epsilon. Below b the function is identically zero on a neighbourhood; above b+epsilon it is affine. Together with the exact interior positive second derivative this yields the sign of the Gaussian cap-kink distributional curvature everywhere outside the two boundary levels (which have zero Gaussian occupation).
-- source:
--   Complete the piecewise source-exact Gaussian cap-kink mollification curvature needed by the genuine finitecap original Itô–Stieltjes ledger, without assuming false classical second-derivative interchange at b.

import Mathlib
open Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
    (b ε y : ℝ) (hε : 0 < ε)
    (hy : y < b ∨ b + ε < y) :
    iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y = 0 := by sorry
