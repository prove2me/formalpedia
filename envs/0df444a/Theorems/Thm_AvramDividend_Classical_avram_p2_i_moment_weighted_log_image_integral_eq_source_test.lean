-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_image_integral_eq_source_test
-- name    : AvramDividend.Classical.avram_p2_i_moment_weighted_log_image_integral_eq_source_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:09:06.797193+00:00
-- url     : https://prove2.me/theorems/09cb3e07-396f-47e1-8fe9-a8a40df2d385
-- title:
--   General weighted exponential log-image real integral equals original negative-supported test integral
-- statement:
--   For any measurable original-space real variable Y and any measurable real test f vanishing at nonnegative marks, the real integral of f(log z)/(z-1)^4 against the fourth-weighted exponential pushforward measure is exactly the original real integral of f(Y). This uses measure integral_map, the real ENNReal withDensity Bochner integration identity and a previously Proved all-real pointwise weighted inverse. No rate convergence or jump identity is assumed. The identity is essential for converting P2-I's Proved weighted-image compact-negative test limit to P2-A's unweighted small-time source test limit.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_weighted_log_image_integral_eq_source_test
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hfpos : ∀ y : ℝ, 0 ≤ y → f y = 0) :
    (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
      ((μ.withDensity (fun ω => ENNReal.ofReal
        ((Real.exp (Y ω) - 1) ^ 4))).map
        (fun ω => Real.exp (Y ω)))) =
    ∫ ω, f (Y ω) ∂μ := by sorry
