-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_pos_of_finite_noAtoms
-- name    : AvramDividend.Classical.continuousOn_measureReal_Ici_pos_of_finite_noAtoms
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T13:51:09.113141+00:00
-- url     : https://prove2.me/theorems/5e0ae1d1-4948-4867-8d7c-9f4e22c9a0e5
-- title:
--   Atomless locally finite positive upper tails are continuous on (0,∞)
-- statement:
--   An atomless measure need not have finite total mass. If its upper tails [x,∞) are finite for every positive x, then the real-valued tail mass is continuous on (0,∞). Around a fixed x>0 choose a=x/2>0; the constant function 1 is integrable on [a,∞), and the pinned upper-tail primitive continuity theorem yields continuity near x.
-- source:
--   Pinned Mathlib IntegrableOn.continuousOn_Ici_primitive_Ici, integrableOn_const_iff and setIntegral_one_eq_measureReal. Local form required by infinite excursion measures.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuousOn_measureReal_Ici_pos_of_finite_noAtoms
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) :
    ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) := by sorry
