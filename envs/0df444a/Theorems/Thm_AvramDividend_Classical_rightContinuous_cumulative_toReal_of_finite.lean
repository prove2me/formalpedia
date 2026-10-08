-- Prove2me | Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
-- name    : AvramDividend.Classical.rightContinuous_cumulative_toReal_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:52:07.258976+00:00
-- url     : https://prove2.me/theorems/b6cea95b-55b1-46d5-b4f7-15d7c45be22d
-- title:
--   Right continuity of an everywhere-finite cumulative measure
-- statement:
--   If β((-∞,x]) is finite for every x, then its real-valued cumulative function is right-continuous at every real point. This is the standard continuity-from-above property of measures applied to decreasing lower intervals.
-- source:
--   Pinned Mathlib measure continuity from decreasing intersections and ENNReal.toReal continuity on finite values. This is the regularity actually needed for the geometric renewal CDF in the Avram BV construction.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem rightContinuous_cumulative_toReal_of_finite
    (β : Measure ℝ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ∞) :
    ∀ x : ℝ,
      ContinuousWithinAt (fun y : ℝ => (β (Iic y)).toReal) (Ici x) x := by
  sorry

end AvramDividend.Classical
