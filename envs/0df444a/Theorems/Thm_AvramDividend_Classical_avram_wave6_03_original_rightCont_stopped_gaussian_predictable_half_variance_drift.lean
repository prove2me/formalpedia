-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:59:35.596408+00:00
-- url     : https://prove2.me/theorems/dbad727a-f846-4274-974c-762e0cc0ece0
-- title:
--   Exact one-half Gaussian quadratic Ito drift for original stopped-history weighted source increments
-- statement:
--   For the actual original pure-Gaussian zero-jump Levy source and its right-continuous filtration, at any bounded stopping time and any integrable predictably measurable source-history weight H with integrable weighted source-increment square, prove the exact L1 half-quadratic Taylor-cell contribution: E[(1/2)*H*(X.X_(tau+h)-X.X_tau-h*c)^2] = (h*sigma^2/2)*E[H]. This exports the correct coefficient sigma^2/2 on original Omega and source path for the controlled discounted Hessian H=e^(-q tau)*w''(U_(tau-)), stopped at ruin and localized, via existing Proved source pre-dividend weight measurability and bounded-H integrability lemmas. Sigma=0 is allowed; no general-nu bracket claim.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHI : Integrable H P)
    (hWeightedInt : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) := by
  sorry
