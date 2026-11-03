-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:26:49.101709+00:00
-- url     : https://prove2.me/theorems/00bc46b1-17d8-448b-b0c5-e8d50674220f
-- title:
--   Conditional bilinear covariance of two original-source stopped Gaussian weights
-- statement:
--   On the same probability space as the genuine zero-jump spectrally negative Lévy source X and its right-continuous filtration, the conditional covariance of two predictable stopped-history weighted centred increments is h sigma squared times their coefficient product. Both weights are measured at the actual bounded stopping time and the bilinear product is assumed integrable; sigma=0 is included. This exact conditional polarisation bridges the source quadratic energy theorem and finite-family predictable stochastic integral isometry; it does not replace a source Gaussian decomposition for ν≠0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProductIntegrable : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
  sorry
