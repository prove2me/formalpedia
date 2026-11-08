-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_original_variable_stopped_gaussian_sum_mean_zero
-- name    : AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_variable_stopped_gaussian_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:28:17.901551+00:00
-- url     : https://prove2.me/theorems/9b2ae05d-1e59-44a9-a86d-2ae013a0d500
-- title:
--   Original zero-negative-jump variable-stopped predictable Gaussian finite sum is centred
-- statement:
--   For the original spectrally negative Levy process with zero negative-jump measure, a finite family of bounded right-continuous stopping times, predictable stopped coefficients, and individually integrable original drift-centred increments, prove the physical Gaussian finite sum is integrable and has expectation zero. This is a reusable exact source component for the zero-jump finite and infinite cap Ito budgets.
-- source:
--   Exact X-as-Y zero-jump source decomposition and an instance of the Proved original stopped Gaussian L1 finite-sum theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_variable_stopped_predictable_linear_L1_sum_mean_zero

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_variable_stopped_gaussian_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
        (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c))) P) :
    Integrable (fun ω => ∑ i ∈ S, G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c))) P ∧
    (∫ ω, ∑ i ∈ S, G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
       (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)) ∂P) = 0 := by sorry
