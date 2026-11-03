-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:37:14.231464+00:00
-- url     : https://prove2.me/theorems/0b2a17a8-8210-45fb-a5c3-f79fd3542828
-- title:
--   True compensated bilinear Gaussian bracket has zero stopped conditional mean
-- statement:
--   For the original zero-jump spectrally negative Lévy process at a bounded right-continuous stopping time, the two genuine predictably weighted centred stochastic increments (G Y) and (H Y) have conditionally compensated bracket (G Y)(H Y)-h sigma squared GH of mean zero at the stopped history, when both GH and its product with Y squared are integrable. This is the centred bilinear martingale-difference form needed for quadratic covariation and discrete integration, including sigma=0, without any auxiliary Brownian copy or claim for ν nonzero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGHInt : Integrable (fun ω => G ω * H ω) P)
    (hProductInt : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
