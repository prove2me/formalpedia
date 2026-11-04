-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:45:40.216774+00:00
-- url     : https://prove2.me/theorems/2c9d0d39-1998-47ca-9bc2-5d03bfce6d7b
-- title:
--   Original Levy fourth-weighted moment rate shares a zeroth-moment upper bound for every order
-- statement:
--   For the genuine original spectrally negative Levy process, every exponentially weighted fourth-moment small-time expectation divided by h is eventually bounded by the same source Lévy zeroth fourth moment plus 1. The threshold in h may depend on moment order k, but the finite bounding constant does not. This follows from independently proved source weighted moment convergence, source Levy integrability and negative-mark comparison.

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_all_moments_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_integral_moment_le_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h <
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by sorry
