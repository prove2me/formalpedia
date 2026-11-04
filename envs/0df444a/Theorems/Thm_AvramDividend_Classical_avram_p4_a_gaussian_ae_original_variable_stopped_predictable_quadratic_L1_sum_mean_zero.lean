-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:18:09.518706+00:00
-- url     : https://prove2.me/theorems/b412ef0b-85bc-4b13-a8f3-90a00085aeeb
-- title:
--   Original Gaussian variable stopped predictable compensated quadratic simple sum has L1 and zero mean
-- statement:
--   For the original spectrally negative Levy source with almost-sure all-times same-space zero-jump Gaussian extraction, any finite collection of distinct genuine bounded stopping clocks and integrable stopped-history Hessian weights yields an integrable total compensated Gaussian square test with exact zero mean. The Gaussian quadratic correction uses sigma squared times elapsed time and also covers sigma zero. Does not assert source decomposition existence, stochastic integral convergence or boundary occupation.
-- source:
--   Accepted source e54533f1-d0de-4e1b-8071-48c98d5f3e78 for genuine right-continuous stopped Gaussian quadratic test; a.e. original source extraction and finite Bochner integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)) ^ 2)) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    Integrable (fun ω => ∑ i ∈ S,
      H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
      (∫ ω, ∑ i ∈ S,
        H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by sorry
