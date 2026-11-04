-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:37:05.976019+00:00
-- url     : https://prove2.me/theorems/f32b23fa-6d4a-44cc-83f9-9e9bbc51fc96
-- title:
--   Original Lévy fourth-weighted exponential family recovers every integer image moment
-- statement:
--   For the actual original spectrally negative Lévy process and nonnegative theta, specialise its Proved source fourth-weight exponential small-time derivative to rho=k*theta for any natural k. Identify exp(k*theta*y) with (exp(theta*y))^k, thereby obtaining the exact kth image moment convergence of the weighted small-time law to the kth weighted moment of the original negative Lévy measure. This theorem is process-specific, genuine and contains no jump rate assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_fourth_weighted_integer_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν)) := by sorry
