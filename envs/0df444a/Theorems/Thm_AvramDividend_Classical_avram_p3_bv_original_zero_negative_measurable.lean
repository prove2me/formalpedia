-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_zero_negative_measurable
-- name    : AvramDividend.Classical.avram_p3_bv_original_zero_negative_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:17:06.84719+00:00
-- url     : https://prove2.me/theorems/1c17a30c-c2f4-4853-b36e-1d9475cd6873
-- title:
--   Measurability of original BV verification function with zero negative-reserve boundary
-- statement:
--   Continuity of the genuine verification function on nonnegative reserves, together with its zero value at strictly negative reserves, implies global Borel measurability across the ruin boundary. This discharges the measurability premise in the original BV physical negative-jump Lévy generator integral.
-- source:
--   Pinned Mathlib ContinuousOn.measurable_piecewise, with s = Ici 0 and g = constant zero; original function equality by zero negative reserve boundary.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p3_bv_original_zero_negative_measurable
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hneg : ∀ y : ℝ, y < 0 → w y = 0) : Measurable w := by sorry
