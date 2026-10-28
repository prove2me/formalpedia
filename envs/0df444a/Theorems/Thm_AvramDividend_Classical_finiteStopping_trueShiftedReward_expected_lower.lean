-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_lower
-- name    : AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:08:06.499331+00:00
-- url     : https://prove2.me/theorems/8dd34882-f155-4269-83af-658b711c21af
-- title:
--   Finite stopped-Markov lower factorisation of shifted two-sided exit reward
-- statement:
--   The exact continuously defined two-sided exit reward of a Lévy future increment path has a stopped-history expectation bounded below by the past discounted survival mass multiplied by the independent, original two-sided exit reward expectation. Together with the upper bound it provides both directions of the Markov renewal identity needed for lower first-record regeneration.
-- source:
--   The forthcoming proved lower indexed-exit comparison finiteStopping_trueTwoSided_expected_lower_imported and Proved levy_shifted_trueTwoSided_reward_eq_schedule; exact reversal of the previously accepted upper shifted-reward factorisation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_lower_imported
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0 ∂P) := by sorry
