-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_time_concatenation
-- name    : AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_time_concatenation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:09:26.207929+00:00
-- url     : https://prove2.me/theorems/298fb3e1-e93c-4091-804b-981a1d072958
-- title:
--   Any marked measure is additive over consecutive right-closed time rectangles
-- statement:
--   For an arbitrary measure on nonnegative time and real jump marks, the mass of the marked rectangle (0,T+S] times B equals the sum of its masses on (0,T] times B and (T,T+S] times B, when B is measurable. The intervals are disjoint and exhaust the horizon. In particular this applies pathwise to the original intrinsic Lévy jump-counting measure without any moment, rate, finite-activity or compensator assumption.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_time_concatenation
    (μ : Measure (ℝ≥0 × ℝ)) (T S : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    μ (Ioc 0 (T + S) ×ˢ B) =
      μ (Ioc 0 T ×ˢ B) + μ (Ioc T (T + S) ×ˢ B) := by sorry
