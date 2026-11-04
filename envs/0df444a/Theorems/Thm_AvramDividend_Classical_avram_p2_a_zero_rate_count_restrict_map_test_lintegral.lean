-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_count_restrict_map_test_lintegral
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_count_restrict_map_test_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:59:55.665249+00:00
-- url     : https://prove2.me/theorems/bd88fc0b-eb07-4064-8135-843eaca58ffa
-- title:
--   Nonnegative marked-test integral against a restricted count-map equals the genuine marked jump sum
-- statement:
--   For a measurable original-jump-time set and a measurable mark map, the integral of a nonnegative measurable mark test against the push-forward of restricted counting measure equals the unconditional ENNReal marked sum over exactly those times. This is the needed measure-theoretic bridge between the canonical intrinsic jump-count map and finite compact-test jump sums; it assumes no stochastic intensity or compensation law.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_count_restrict_map_test_lintegral
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (J : Set α) (hJ : MeasurableSet J)
    (j : α → β) (hj : Measurable j)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂((Measure.count.restrict J).map j)) =
      ∑' x : α, J.indicator (fun y => g (j y)) x := by sorry
