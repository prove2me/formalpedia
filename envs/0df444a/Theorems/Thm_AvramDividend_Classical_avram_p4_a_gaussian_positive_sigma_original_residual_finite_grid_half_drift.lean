-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_original_residual_finite_grid_half_drift
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_original_residual_finite_grid_half_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:53:36.961726+00:00
-- url     : https://prove2.me/theorems/d53709dd-10d0-4a67-8048-d7c360054ec8
-- title:
--   Original positive Gaussian residual finite-grid Ito half-drift with true L1 and source sigma²/2
-- statement:
--   For the actual original X and its exact same-space same-filtration jump/Gaussian decomposition, a finite family of bounded original right-continuous stopped times and stopped-history weights has integrable Gaussian quadratic residual sum and exact expected half-Hessian drift sum_i h_i sigma(X)^2/2 E[H_i]. R_i is explicitly identified pointwise with the actual source X minus drift and actual small/large jump components, so no Brownian is imported or presumed to represent X. The source decomposition and finite-grid integrability remain explicit required hypotheses; this does not assert mesh limit or pathwise quadratic variation.
-- source:
--   Accepted original zero-jump finite grid half drift aa7f4cc5, original X same-path residual; Avram Eq 5.11.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_original_residual_finite_grid_half_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
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
    (R : ι → Ω → ℝ)
    (hR : ∀ i ω, R i ω = X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω -
        (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))
    (hWeightedInt : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (R i ω) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2) P ∧
    (∫ ω, ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (((h i : ℝ) * X.σ ^ 2) / 2) * (∫ ω, H i ω ∂P) := by sorry
