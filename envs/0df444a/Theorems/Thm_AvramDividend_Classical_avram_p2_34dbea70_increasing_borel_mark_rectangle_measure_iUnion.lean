-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion
-- name    : AvramDividend.Classical.avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:55.97121+00:00
-- url     : https://prove2.me/theorems/71cd3aab-df54-4269-bdec-445bf8fc7fd0
-- title:
--   Increasing Borel mark rectangles converge in original time-mark measure
-- statement:
--   For any measure on nonnegative time and real jump marks, the measure of a rectangle whose mark set is an increasing countable union equals the supremum of measures of the individual marked rectangles. This is a deterministic continuity-from-below result applicable to the original intrinsic marked jump counting measure, without compensation or a Levy rate hypothesis.

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_increasing_borel_mark_rectangle_measure_iUnion (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : Monotone B) :
    μ (Ioc 0 T ×ˢ (⋃ n, B n)) =
      ⨆ n, μ (Ioc 0 T ×ˢ B n) := by sorry
