-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_positive_strict_tail_of_absolutelyContinuous
-- name    : AvramDividend.Classical.continuousOn_positive_strict_tail_of_absolutelyContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:12:28.165256+00:00
-- url     : https://prove2.me/theorems/5f5133a3-6823-4c1e-af8a-017d0028a356
-- title:
--   Positive strict tail mass is continuous for absolutely continuous locally finite measures
-- statement:
--   If a real measure is absolutely continuous with respect to Lebesgue measure and finite on every positive upper ray, its real strict-tail mass μ((x,∞)) is continuous on x>0. Absolute continuity supplies the null-singleton instance; use the already proved strict-tail continuity theorem.
-- source:
--   Absolutely continuity transfers Lebesgue singleton nullity to the measure; invoke the canonical strict upper-tail continuity result.

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
open MeasureTheory Set

namespace AvramDividend.Classical
theorem continuousOn_positive_strict_tail_of_absolutelyContinuous
    (μ : Measure ℝ) (hac : μ ≪ volume)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ioi x)) (Ioi 0) := by sorry
end AvramDividend.Classical
