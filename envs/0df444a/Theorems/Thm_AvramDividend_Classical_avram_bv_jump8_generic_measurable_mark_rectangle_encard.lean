-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
-- name    : AvramDividend.Classical.avram_bv_jump8_generic_measurable_mark_rectangle_encard
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:34:11.402206+00:00
-- url     : https://prove2.me/theorems/2d4b5e19-a4a6-43c3-929c-a607ace9b825
-- title:
--   Generic càdlàg marked counting measure equals cardinality of its actual time-mark rectangle
-- statement:
--   For an arbitrary real-valued path with Borel measurable intrinsic time-jump-mark map, the exact restricted counting-measure image of a measurable Borel time and mark rectangle equals the extended natural cardinality of corresponding marked jump times. No Lévy law or stochastic hypotheses are used.
-- source:
--   Generalises the accepted original-specific rectangle-encard proof f6336d40 to arbitrary Borel marked path. Used with the original shifted path to close the same-path clock-translation target 5714bfe7.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_generic_measurable_mark_rectangle_encard
    (Y : ℝ≥0 → ℝ)
    (hMark : Measurable (fun u : ℝ≥0 =>
      (u, Y u - Function.leftLim Y u)))
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Y u - Function.leftLim Y u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      Y u - Function.leftLim Y u ≠ 0 ∧
      Y u - Function.leftLim Y u ∈ B}).encard := by sorry
