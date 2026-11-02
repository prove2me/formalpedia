-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_grid_compensated_quadratic_mean_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_grid_compensated_quadratic_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:14:28.642551+00:00
-- url     : https://prove2.me/theorems/ef74fe26-aa1b-4048-933c-bd3553b08528
-- title:
--   Finite-grid original Gaussian predictable quadratic residual is an integrable exactly centered martingale test
-- statement:
--   For a finite family of original right-continuous stopping times of the same zero-jump spectrally negative Levy process, stopped-history measurable coefficients with explicit L1 assumptions, the sum of all predictable Hessian-like coefficients times each true centered Gaussian increment squared minus its variance h_i sigma^2 is integrable and has expectation exactly zero. This is the finite-grid quadratic compensator cancellation needed for the Gaussian sigma-squared-over-two second derivative drift; it makes no independent-Brownian or full semimartingale bracket claim, and allows sigma zero. Individual clocks need not be disjoint because only linearity of expectation is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_grid_compensated_quadratic_mean_zero
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
      (fun ω => H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S, H i ω * ((X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S, H i ω * ((X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  sorry
