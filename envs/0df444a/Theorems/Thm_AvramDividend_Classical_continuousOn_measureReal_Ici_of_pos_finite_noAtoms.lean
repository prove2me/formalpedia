-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_pos_finite_noAtoms
-- name    : AvramDividend.Classical.continuousOn_measureReal_Ici_of_pos_finite_noAtoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:52:28.324199+00:00
-- url     : https://prove2.me/theorems/8e22af94-7f06-47e6-ac72-eaf1ca609dc6
-- title:
--   Atomless upper-tail mass is continuous on positive thresholds under local finiteness
-- statement:
--   If a measure on the real line has no singleton atoms and every strictly positive upper tail [x,∞) has finite mass, then x↦μ([x,∞)) is continuous on (0,∞). No finiteness at zero or negative thresholds is required. This matches excursion-height measures, which may have infinite total mass while having finite tails above every positive height.
-- source:
--   Localised use of pinned Mathlib MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ici and setIntegral_one_eq_measureReal.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuousOn_measureReal_Ici_of_pos_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) := by sorry
