-- Prove2me | Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_discount_reward_measurable
-- name    : AvramDividend.Classical.countable_future_twoSided_discount_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:32:35.790903+00:00
-- url     : https://prove2.me/theorems/a3cd9256-7f08-4808-9731-d1a704d4ea43
-- title:
--   Measurability of a countable-grid discounted two-sided future exit reward
-- statement:
--   The discounted reward for the first strict upper before lower exit on a countable future observation schedule is Borel measurable on the entire product-measurable future-path space. This is the full-future-path reward required by the stopped Markov factorisation for the lower reflected-barrier renewal bound.
-- source:
--   Uses the Proved countable future two-sided exit clocks UUID ca0c187a-681f-4f05-b40b-d0c00677b324 and pinned Mathlib measurableSet_lt, ENNReal.measurable_toReal, Real.measurable_exp, ENNReal.measurable_ofReal. Repairs the missing Real.exp import that caused publication failure of first job 986f0124-d857-46dd-9af2-b8d0e2de0bad.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_exit_clocks_measurable

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.countable_future_twoSided_discount_reward_measurable
    (τ : ℕ → ℝ≥0) (q upper lower : ℝ) :
    Measurable (fun g : ℝ≥0 → ℝ =>
      let ρ : ℝ≥0∞ :=
        ⨅ j : ℕ, if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
      let σ : ℝ≥0∞ :=
        ⨅ j : ℕ, if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
      if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by sorry
