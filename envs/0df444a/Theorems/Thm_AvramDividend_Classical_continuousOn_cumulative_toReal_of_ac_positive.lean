-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_cumulative_toReal_of_ac_positive
-- name    : AvramDividend.Classical.continuousOn_cumulative_toReal_of_ac_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:45:42.374576+00:00
-- url     : https://prove2.me/theorems/c35242c6-5e18-4bde-8dbf-d37dd64ef351
-- title:
--   Continuity of a locally finite cumulative measure on an atom-free positive half-line
-- statement:
--   Let β be a measure on the real line whose cumulative mass β((-∞,x]) is finite for every x. If β restricted to (0,∞) is absolutely continuous with respect to Lebesgue measure, then x↦β((-∞,x]).toReal is continuous on (0,∞). Right continuity is the usual continuity-from-above property of measures; the left jump at x is β({x}), which vanishes on the positive half-line by absolute continuity.
-- source:
--   Pinned Mathlib measure continuity from monotone set limits, measure_sdiff, volume_singleton, ENNReal.toReal, and Monotone.continuousAt_iff_leftLim_eq_rightLim. This generic CDF regularity bridge is needed to identify the Avram bounded-variation geometric renewal cumulative pointwise by Laplace uniqueness.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- If every lower cumulative interval has finite mass and the restriction of a measure to the positive half-line is absolutely continuous with respect to Lebesgue measure, then its real-valued cumulative function is continuous on the positive half-line. -/
theorem continuousOn_cumulative_toReal_of_ac_positive
    (β : Measure ℝ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ∞)
    (hac : β.restrict (Ioi (0 : ℝ)) ≪ (volume : Measure ℝ)) :
    ContinuousOn (fun x : ℝ => (β (Iic x)).toReal) (Ioi (0 : ℝ)) := by
  sorry

end AvramDividend.Classical
