-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero
-- name    : AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:30:50.914195+00:00
-- url     : https://prove2.me/theorems/ba7b6ee6-a230-4f33-93a2-a0dc22d9c375
-- title:
--   Original bounded stopped Gaussian drift-centred finite grid is L1 and has zero mean
-- statement:
--   For the actual original zero-negative-jump Levy process and an arbitrary finite grid of bounded right-continuous stops, each bounded stopped-measurable predictable weight multiplying the original drift-centred Gaussian increment is integrable, and their sum has expectation zero. No separate cell integrability is assumed.
-- source:
--   The Proved source-exact bounded stopped Gaussian L2 increment result, followed by finite-sum integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_bounded_stopped_gaussian_grid_mean_zero
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
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    Integrable (fun ω => ∑ i ∈ S, G i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)) P ∧
    (∫ ω, ∑ i ∈ S, G i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by sorry
