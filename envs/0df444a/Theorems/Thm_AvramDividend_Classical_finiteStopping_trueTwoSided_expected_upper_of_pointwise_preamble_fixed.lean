-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
-- name    : AvramDividend.Classical.finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:36:52.993235+00:00
-- url     : https://prove2.me/theorems/e1b20c8c-aebb-409a-8022-fba634156e9d
-- title:
--   Finite stopped Markov factorisation with correctly imported stopping-time construction
-- statement:
--   For finite right-continuous Levy stopping clocks, a pointwise discounted shifted-grid two-sided reward upper bound factors into the expected stopped discount and exact two-sided first-exit expectation. This theorem supplies the required stopping-time construction import missing from an earlier original problem.
-- source:
--   Verified stopped Markov expected inequality and countable-grid equality of strict two-sided exit rewards.

import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_trueTwoSided_discount_reward_eq_countable_schedule

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) (weight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, weight ω ≤
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0)) :
    (∫⁻ ω, weight ω ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                    (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by sorry
