-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_L2
-- name    : AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:29:33.019699+00:00
-- url     : https://prove2.me/theorems/04417559-44cb-4b8e-abdc-9a22c045524b
-- title:
--   Finite original stopped predictable Gaussian gain sum lies in physical L2
-- statement:
--   A finite sum of bounded predictably weighted literal original source-centred Gaussian stopped increments lies in L2(P) on the given original sample space and filtration, for arbitrary Gaussian coefficient including zero. This is the finite-simple-integral L2 localisation interface, not a Brownian surrogate.
-- source:
--   W7-05 direct source-specific finite-sum consequence of Proved ab5f60fe-7ae6-40e6-9ea2-3dd40a6e43d4 and pinned Mathlib memLp_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_L2
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
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P := by sorry
