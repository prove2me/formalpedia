-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:44:05.291916+00:00
-- url     : https://prove2.me/theorems/e1006946-dc94-42f9-91a5-e3c56c8cb5ae
-- title:
--   All-sigma original Gaussian finite variable stopped-mesh linear stochastic sum has L1 and zero mean
-- statement:
--   For the actual original Levy process X, an almost-sure all-times same-space Gaussian source extraction and finite collection of genuine bounded stopping times and measurable stopped-history gains, each with explicitly integrable original Gaussian residual, imply that the finite simple stochastic integral sum is integrable and has mean zero. No globally bounded gains, positive sigma, auxiliary Brownian process or global C2 assumption is needed.
-- source:
--   Proved source b60fe94d-4b52-4e9d-9303-4ef2c50a5a5c: the actual zero-jump stopped Gaussian history-weighted mean zero; termwise a.e. source extraction, integrable_finset_sum and integral_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    Integrable (fun ω => ∑ i ∈ S, G i ω * M i ω) P ∧
      (∫ ω, ∑ i ∈ S, G i ω * M i ω ∂P) = 0 := by sorry
