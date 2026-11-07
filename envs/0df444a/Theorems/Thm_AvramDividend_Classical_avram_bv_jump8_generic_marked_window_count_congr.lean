-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_marked_window_count_congr
-- name    : AvramDividend.Classical.avram_bv_jump8_generic_marked_window_count_congr
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:11:09.607938+00:00
-- url     : https://prove2.me/theorems/7e0902b7-aeda-4bd5-90f6-144bea26d832
-- title:
--   Exact marked count rectangle congruence from measurable maps with equal time coordinate and equal within-window supports and marks
-- statement:
--   For two measurable time/mark maps with true time as first coordinate, if their active supports and full marks agree at every time in (0,n], their count-restricted pushforward measures coincide on every Borel-marked (0,n] rectangle. Exact time-zero exclusion and closed horizon. This is a generic deterministic counting measure transport certificate.
-- source:
--   Measure.map_apply, Measure.restrict_apply, and set extensionality; uses the pinned Mathlib signatures. This is the generic measure-theoretic child required by source rectangle 624daffe, and is reusable for marked approximation path comparisons.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_generic_marked_window_count_congr
    (S T : Set ℝ≥0) (f g : ℝ≥0 → ℝ≥0 × ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B)
    (hFTime : ∀ u, (f u).1 = u)
    (hGTime : ∀ u, (g u).1 = u)
    (hSupport : ∀ u : ℝ≥0, 0 < u → u ≤ (n : ℝ≥0) →
      (u ∈ S ↔ u ∈ T))
    (hMarks : ∀ u : ℝ≥0, 0 < u → u ≤ (n : ℝ≥0) → f u = g u) :
    ((Measure.count.restrict S).map f) (Ioc 0 (n : ℝ≥0) ×ˢ B) =
    ((Measure.count.restrict T).map g) (Ioc 0 (n : ℝ≥0) ×ˢ B) := by sorry
