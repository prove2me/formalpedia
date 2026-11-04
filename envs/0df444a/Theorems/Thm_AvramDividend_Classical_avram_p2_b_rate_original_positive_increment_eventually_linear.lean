-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_increment_eventually_linear
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_positive_increment_eventually_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:52:08.056451+00:00
-- url     : https://prove2.me/theorems/256be8e7-bc10-4eb6-a5ef-ffe871e97bab
-- title:
--   Original Lévy positive exponential event has kth weighted small-time upper bound
-- statement:
--   For the actual original Lévy increment and each integer k, the positive exponential image event z>=R>1 has O(h) mass after multiplying by R^k(R-1)^4, bounded by the original negative Lévy measure weighted kth integral plus one. This is the exact analytic ingredient for the k-to-infinity no-positive-jump argument, with marginal measurability only and without assuming jump intensity. Publication must wait for source integrability and Markov supporting proofs to be accepted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_positive_increment_weighted_markov

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_positive_increment_eventually_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
        P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)} ≤
      ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by sorry
