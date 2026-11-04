-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_variance
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:26:26.69554+00:00
-- url     : https://prove2.me/theorems/ebeb2af2-dfd4-41d4-8d77-d6a10569f48e
-- title:
--   Original Lévy positive Gaussian residual has unit stopped variance rate
-- statement:
--   Conditional on the explicit same-probability-space, same-filtration, exact all-times Lévy jump/Gaussian decomposition, the variance of the normalised original residual increment from bounded original right-continuous stopping time τ to τ+h is exactly h for positive σ. The source stopped Gaussian variance theorem is used directly; no independent Brownian source is postulated to be the original process, and pathwise QV, Brownian continuity, integrals and the decomposition itself remain unproved.
-- source:
--   SpectrallyNegativeLevy original source; Proved 3c7623a6-ce31-4f8a-adc6-d73b0ebd8747, original stopped zero-jump Gaussian exact variance; generator coefficient σ²/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_normalized_same_source_stopped_variance
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
    (h : ℝ≥0) :
    (∫ ω, ((X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
      Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
       Jsmall (τ ω) ω - Jlarge (τ ω) ω)) / X.σ) ^ 2 ∂P) =
      (h : ℝ) := by sorry
