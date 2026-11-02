-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:07:59.525001+00:00
-- url     : https://prove2.me/theorems/aa7f4cc5-11d6-4a3a-adea-c49d150af3e7
-- title:
--   True finite-grid source Gaussian Ito Hessian sums have exact sigma-squared-over-two drift
-- statement:
--   For any finite family of right-continuous bounded stopping times of the original no-jump spectrally negative Levy source, with stopped-history predictable coefficients H_i and explicit integrability of H_i and H_i times the true squared drift-centered source increment, prove that the sum of one-half H_i times squared true source Gaussian increments is L1 and has exact expectation sum_i h_i sigma^2/2 E[H_i]. This is the precise original-process Gaussian quadratic Ito drift at finite predictable grids, preserving arbitrary sigma including zero and enabling discounted pre-dividend Hessian weights from existing controlled-sigma results. It uses no auxiliary Brownian copy and asserts no general-jump bracket or full mesh limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_half_variance_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i : ι, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHstop : ∀ i : ι,
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hWeightedInt : ∀ i ∈ S, Integrable
      (fun ω => H i ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, ∑ i ∈ S, (1 / 2 : ℝ) * H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 ∂P) =
      ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H i ω ∂P) := by
  sorry
