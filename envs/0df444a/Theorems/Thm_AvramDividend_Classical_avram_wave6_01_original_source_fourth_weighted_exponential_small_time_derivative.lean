-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
-- name    : AvramDividend.Classical.avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:30:39.089364+00:00
-- url     : https://prove2.me/theorems/e6973988-8944-43a3-936c-4fe904297c04
-- title:
--   Actual source small-time fourth-weighted exponential expectation recovers Lévy weighted moment
-- statement:
--   For the given original spectrally negative Lévy process on its actual probability space, and nonnegative real shift and mark rates, the first-order small-time rate of E[exp(rho X_h)(exp(theta X_h)-1)^4] equals the original negative Lévy measure integral of the same fourth-weighted exponential mark function. It is derived from the actual independent stationary increment Laplace transform and the source shifted exponent finite difference, without assuming a jump compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_finite_exponential_test_small_time_source_derivative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        (∫ ω, Real.exp (ρ * X.X (Real.toNNReal h) ω) *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν)) := by sorry
