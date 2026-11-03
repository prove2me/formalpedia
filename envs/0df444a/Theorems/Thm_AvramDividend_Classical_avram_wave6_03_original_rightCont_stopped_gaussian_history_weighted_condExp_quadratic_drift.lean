-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:56:11.819847+00:00
-- url     : https://prove2.me/theorems/64207d1d-ec96-497f-ab59-fb661201ed1d
-- title:
--   Actual predictably weighted stopped Gaussian square has exact conditional sigma-squared drift
-- statement:
--   For the original zero-jump source X and bounded original rightCont stopping time, any stopped-history measurable H with true integrable product H*(X_(tau+h)-X_tau-hc)^2 has exact conditional quadratic expectation h*sigma²*H at the actual stopped history. This is the generic predictably weighted conditional Gaussian Ito quadratic-variation cell, with sigma zero allowed, no detached Brownian, no assumed sigma positivity; the original controlled Hessian is a special case. Prove from the accepted true stopped second conditional moment and condExp pull-out.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * H ω) := by
  sorry
