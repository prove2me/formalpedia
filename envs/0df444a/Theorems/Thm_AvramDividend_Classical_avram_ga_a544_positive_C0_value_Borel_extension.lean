-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a544_positive_C0_value_Borel_extension
-- name    : AvramDividend.Classical.avram_ga_a544_positive_C0_value_Borel_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:44:58.412527+00:00
-- url     : https://prove2.me/theorems/593844df-c8b6-42e6-bdf1-2ccc4b74616e
-- title:
--   Positive-half-line continuous function with a constant nonpositive extension is measurable
-- statement:
--   A real-valued function continuous on strictly positive reals extends to a globally measurable function by using its value at zero on nonpositive reals. This handles stopped endpoints at zero without imposing global regularity of w.
-- source:
--   Mathlib ContinuousOn.measurable_piecewise for measurable positive half-line and continuous constant complement

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_ga_a544_positive_C0_value_Borel_extension
    (w : ℝ → ℝ) (hw : ContinuousOn w (Set.Ioi (0 : ℝ))) :
    Measurable (fun y : ℝ => if 0 < y then w y else w 0) := by sorry
