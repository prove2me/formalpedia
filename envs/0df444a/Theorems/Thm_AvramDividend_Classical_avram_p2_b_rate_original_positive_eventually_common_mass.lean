-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_eventually_common_mass
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_positive_eventually_common_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:53.058405+00:00
-- url     : https://prove2.me/theorems/aa765a5e-55c3-491c-b04f-557ff235be09
-- title:
--   Original Levy positive exponential-image event has uniform all-order eventual mass bound
-- statement:
--   For the actual original Levy process with measurable marginals, every kth positive exponential-image Markov inequality has the same finite zeroth negative Lévy weighted mass upper coefficient. Only the small-time neighbourhood may depend on k. This is the source-specific all-power tail squeeze needed to show superunit exponential-image event rate is negligible. No jump-rate assumption.

import Mathlib
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_increment_eventually_linear
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_all_moments_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_integral_moment_le_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_positive_eventually_common_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
        P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)} ≤
      ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by sorry
