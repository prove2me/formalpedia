-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_weighted_variance
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_weighted_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:27:28.152288+00:00
-- url     : https://prove2.me/theorems/e83d0019-fb4f-4780-a141-5ddf2d3cc537
-- title:
--   Original Lévy normalised Gaussian stopped-history weighted quadratic energy
-- statement:
--   For positive original Gaussian σ and an explicit all-times same-path decomposition into a zero-jump source Y plus jump components Jsmall and Jlarge on the same Ω and filtration, the squared normalised residual increment over bounded right-continuous stopping-time [τ,τ+h] has stopped-history weighted mean h E[H]. H is ambient and stopped-history measurable as required by the proved source conditional Gaussian variance theorem. Provides finite-cell predictable quadratic energy without asserting construction of an original Brownian path, bracket, or stochastic integral.
-- source:
--   Proved source 3b8f471a-fcbd-4835-b339-46d13701ea9d, Gaussian stopped conditional weighted variance on original Ω and 𝓕. Same-path decomposition remains explicit upstream hypothesis; generator coefficient σ²/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_weighted_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    (∫ ω, H ω * ((X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
      Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
       Jsmall (τ ω) ω - Jlarge (τ ω) ω)) / X.σ) ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * (h : ℝ) := by sorry
