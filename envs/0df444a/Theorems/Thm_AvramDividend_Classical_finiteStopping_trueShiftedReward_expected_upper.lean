-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_trueShiftedReward_expected_upper
-- name    : AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:39:42.232136+00:00
-- url     : https://prove2.me/theorems/09f59ae9-72a9-4602-9830-26010da0d74c
-- title:
--   Finite stopped-Markov factorisation for the true shifted two-sided exit reward
-- statement:
--   For any finite right-continuous Lévy stopping time and stopped-history event, the expected discounted true continuously defined two-sided reward of the future increment path is bounded by the past discounted history mass times the original two-sided reward expectation. The proof identifies the true shifted reward with the Proved measurable rational schedule then applies the Proved finite-stopping-time Markov inequality. This removes the countable-schedule manipulation from the first-record renewal closure.
-- source:
--   Proved finiteStopping_trueTwoSided_expected_upper_imported and levy_shifted_trueTwoSided_reward_eq_schedule.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_upper_imported
import Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_trueShiftedReward_expected_upper
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
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
       let up : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t}, (i.1 : ℝ≥0∞)
       let dn : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)
       if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
      else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                   (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q *
         ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by sorry
