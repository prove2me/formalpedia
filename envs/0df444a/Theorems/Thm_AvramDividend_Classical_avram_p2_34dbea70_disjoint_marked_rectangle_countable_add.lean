-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_disjoint_marked_rectangle_countable_add
-- name    : AvramDividend.Classical.avram_p2_34dbea70_disjoint_marked_rectangle_countable_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:14:23.026375+00:00
-- url     : https://prove2.me/theorems/22c0bbce-96b1-4330-9a94-295dd0b78ecd
-- title:
--   Countable additivity across disjoint Borel jump marks
-- statement:
--   For an arbitrary measure on time-mark space and pairwise disjoint measurable mark sets, the measure of the corresponding union of marked rectangles equals the ENNReal sum of the rectangle measures.

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_disjoint_marked_rectangle_countable_add (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (Function.onFun Disjoint B)) :
    μ (Ioc 0 T ×ˢ (⋃ n, B n)) =
      ∑' n, μ (Ioc 0 T ×ˢ B n) := by sorry
