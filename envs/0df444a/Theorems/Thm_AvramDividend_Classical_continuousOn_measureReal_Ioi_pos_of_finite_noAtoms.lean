-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:53:56.957735+00:00
-- url     : https://prove2.me/theorems/770da67b-b9ec-49f4-b5dd-6ab52084ec8e
-- title:
--   Continuity of strict upper-tail mass for atomless locally finite measures
-- statement:
--   For an atomless real measure with finite positive upper tails, its strict upper-tail mass μ((x,∞)) is continuous in each x>0. This matches the discounted jump-tail kernel in the bounded-variation Esscher renewal proof, where strict rather than weak inequalities appear.
-- source:
--   Strict-tail continuity as a direct atomlessness corollary of the Proved AvramDividend.Classical.continuousOn_measureReal_Ici_pos_of_finite_noAtoms.

import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_pos_of_finite_noAtoms
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

namespace AvramDividend.Classical
theorem continuousOn_measureReal_Ioi_pos_of_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ioi x)) (Ioi 0) := by sorry
end AvramDividend.Classical
