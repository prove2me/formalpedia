-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_finite_weighted_mark_count_real_sum
-- name    : AvramDividend.Classical.avram_p2_a_assist_finite_weighted_mark_count_real_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:30:59.816363+00:00
-- url     : https://prove2.me/theorems/4e28af6a-3db8-4ab5-b155-434d1208c5d4
-- title:
--   Finite marked jump-count integral equals the genuine real jump sum
-- statement:
--   For a measurable marking map j on a count-restricted set J and a nonnegative measurable real test g with exactly finite nonzero support F, convert the ENNReal integral against the genuine pushforward counting measure to the ENNReal embedding of the original finite real sum. This is the missing deterministic identity needed to match P2-A's integrable pathwise J with the P2-D Tonelli expectation and then X.ν.

import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_count_restrict_map_test_lintegral

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_a_assist_finite_weighted_mark_count_real_sum
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [MeasurableSpace β]
    (J : Set α) (hJ : MeasurableSet J)
    (j : α → β) (hj : Measurable j)
    (g : β → ℝ) (hg : Measurable g)
    (hgnonneg : ∀ y : β, 0 ≤ g y)
    (F : Finset α)
    (hF : ∀ x : α, x ∈ F ↔ x ∈ J ∧ g (j x) ≠ 0) :
    (∫⁻ y, ENNReal.ofReal (g y) ∂((Measure.count.restrict J).map j)) =
      ENNReal.ofReal (∑ x ∈ F, g (j x)) := by sorry
