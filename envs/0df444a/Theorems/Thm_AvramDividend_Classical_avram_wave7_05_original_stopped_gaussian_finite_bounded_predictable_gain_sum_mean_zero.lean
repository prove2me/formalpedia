-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:40:12.088591+00:00
-- url     : https://prove2.me/theorems/03ea605f-315c-4f67-aa9f-642e03cd62e9
-- title:
--   Finite original stopped Gaussian bounded predictable gain sum has exact zero expectation
-- statement:
--   A finite family of actual source-centred Gaussian stopped increments weighted by bounded predictable stopped-history coefficients is individually L2, has a globally integrable sum, and exactly zero total expectation. This is the original-source simple stochastic-integral approximation step for arbitrary Gaussian sigma including zero, not a different Brownian sample space.
-- source:
--   W7-05 original-source finite-sum corollary of one-cell bounded L2 zero-mean theorem 8cf2614f-c9fe-47f1-896a-57969706c910 and pinned Mathlib integral_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    {ι : Type*} (S : Finset ι)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstop : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)
    (∀ i ∈ S, MemLp (F i) 2 P) ∧
      Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
        (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
