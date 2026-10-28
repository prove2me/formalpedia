-- Prove2me | Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_lower_imported
-- name    : AvramDividend.Classical.finiteStopping_trueTwoSided_expected_lower_imported
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:00:47.492249+00:00
-- url     : https://prove2.me/theorems/7763e44c-1dfb-4287-a9a0-20b162f88762
-- title:
--   Finite stopped-Markov lower bound for the actual two-sided exit reward
-- statement:
--   A pathwise lower domination of a killed record reward by the discounted shifted two-sided exit payoff implies a lower bound on its expectation. The independent factor is the exact continuously indexed two-sided exit expectation. This fills the lower counterpart of the proved upper Markov factorisation and is needed for lower first-record renewal.
-- source:
--   Proved stoppedMarkov_pointwise_record_lower_to_expectation_rightCont and exact levy_trueTwoSided_discount_reward_eq_countable_schedule; adapted from the previously accepted upper comparison while preserving the lower inequality direction.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.CompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_trueTwoSided_discount_reward_eq_countable_schedule

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finiteStopping_trueTwoSided_expected_lower_imported
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
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0) ≤ weight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                    (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, weight ω ∂P) := by sorry
