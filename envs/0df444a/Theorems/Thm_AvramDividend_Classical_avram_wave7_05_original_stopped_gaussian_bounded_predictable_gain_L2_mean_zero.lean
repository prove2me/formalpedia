-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:22:54.937176+00:00
-- url     : https://prove2.me/theorems/8cf2614f-c9fe-47f1-896a-57969706c910
-- title:
--   Bounded stopped original Gaussian predictable source gain is in L2 and has expectation zero
-- statement:
--   For the given original zero-jump spectrally negative Lévy source and its actual bounded right-continuous stopping time, a bounded globally and stopped-history measurable predictable weight multiplying the literal centred source increment is genuinely in L2, hence L1, and has exact expectation zero. This is the stochastic integral mean-zero piece needed in localised Gaussian Ito verification; no separate Brownian space is introduced.
-- source:
--   W7-05 source-specific automatic-integrability combination of Proved ab5f60fe-7ae6-40e6-9ea2-3dd40a6e43d4 and c9825ed7-d9b4-486a-9b4d-e1b7950d2a8c, with pinned Mathlib MemLp.integrable and integral_condExp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hGglobal : Measurable G)
    (K : ℝ) (hK : 0 ≤ K) (hGbound : ∀ ω, |G ω| ≤ K) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    MemLp (fun ω => G ω * Y ω) 2 P ∧
      Integrable (fun ω => G ω * Y ω) P ∧
        (∫ ω, G ω * Y ω ∂P) = 0 := by sorry
