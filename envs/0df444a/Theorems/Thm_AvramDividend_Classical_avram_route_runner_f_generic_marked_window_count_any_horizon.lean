-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_generic_marked_window_count_any_horizon
-- name    : AvramDividend.Classical.avram_route_runner_f_generic_marked_window_count_any_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:25:23.246489+00:00
-- url     : https://prove2.me/theorems/52790f3a-3a41-445b-ab6d-3ff281c321ef
-- title:
--   Original measurable time-mark pushforwards preserve arbitrary half-open marked windows
-- statement:
--   For every nonnegative real horizon T, if two measurable time-mark maps have equal support and values on the genuine half-open window (0,T], their restricted counting measure pushforwards agree on each Borel marked rectangle. This extends an established integer-window transport theorem to fractional stopping-time grids without altering endpoints.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_generic_marked_window_count_any_horizon
    (S U : Set ℝ≥0) (f g : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hFTime : ∀ u, (f u).1 = u)
    (hGTime : ∀ u, (g u).1 = u)
    (hSupport : ∀ u : ℝ≥0, 0 < u → u ≤ T →
      (u ∈ S ↔ u ∈ U))
    (hMarks : ∀ u : ℝ≥0, 0 < u → u ≤ T → f u = g u) :
    ((Measure.count.restrict S).map f) (Ioc 0 T ×ˢ B) =
    ((Measure.count.restrict U).map g) (Ioc 0 T ×ˢ B) := by sorry
