-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:45:52.125912+00:00
-- url     : https://prove2.me/theorems/052cba2b-60d6-45af-a744-9913ab2c369f
-- title:
--   Original varying-stopped C2 Gaussian predictable Taylor mesh L1 and mean zero with sigma squared half
-- statement:
--   For genuine variable stopping times on the actual original jump-bearing Levy process X, an almost-sure same-space Gaussian extraction, stopped-history predictable weights and explicit L1 gain conditions imply the full finite stochastic Taylor sum is integrable and has exact zero expectation. The Hessian correction is sigma squared divided by two. Works for sigma zero and positive, with no globally bounded derivatives or Brownian process assumption. Decomposition existence, interior localisation and continuum Ito limit remain separately open.
-- source:
--   Combination of published Gaussian finite L1 linear and compensated-square variable-stop helpers by finite-sum linearity and exact one-half scaling. Dependencies must be Proved before this proof can be accepted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_full_taylor_L1_sum_mean_zero
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
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i))
    (hHstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))) P)
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
      (G i ω * M i ω + (1 / 2 : ℝ) * H i ω *
        (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
      (∫ ω, (∑ i ∈ S,
        (G i ω * M i ω + (1 / 2 : ℝ) * H i ω *
          (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) = 0 := by sorry
