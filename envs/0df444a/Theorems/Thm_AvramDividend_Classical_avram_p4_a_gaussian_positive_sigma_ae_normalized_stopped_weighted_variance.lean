-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_ae_normalized_stopped_weighted_variance
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_normalized_stopped_weighted_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:06:45.910195+00:00
-- url     : https://prove2.me/theorems/a7bdbc48-0dd6-4b92-82e1-3ee4e7ad219a
-- title:
--   Original stopped-history Gaussian predictable weighted variance under an almost-sure source decomposition
-- statement:
--   The actual spectrally negative Lévy X has exact Gaussian weighted stopped variance h after normalizing by its source sigma, provided an almost-sure all-times same-source Levy-Ito decomposition with a jump-free component Y in the original filtration. Uses original bounded stop and original stopped-history measurable H. Does not posit a newly independent Brownian motion or prove the decomposition.
-- source:
--   Accepted source original stopped weighted Gaussian variance e83d0019; original pure Gaussian predictable weighted variance; Avram Eq(5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_normalized_stopped_weighted_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
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
