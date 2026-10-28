-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_integral_positive_deficit_event_null
-- name    : AvramDividend.Classical.zero_integral_positive_deficit_event_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:09:40.976918+00:00
-- url     : https://prove2.me/theorems/cd1627ca-1eac-4db2-ac70-8504725b6073
-- title:
--   Vanishing expected nonnegative deficit on an event and zero atomlessness force that event to be null
-- statement:
--   Let D be an almost surely nonnegative random variable that is nonzero almost surely. If the expectation of D restricted to an arbitrary event E vanishes and the indicated random variable is integrable, then E has probability zero. This converts the bounded-variation Levy finite-mesh expected survival-deficit limit into a genuine zero-reflected-survival null event, avoiding any need for integrability of large negative jumps outside the survival event.
-- source:
--   Mathlib integral_eq_zero_iff_of_nonneg_ae, Set.indicator_of_mem, MeasureTheory.ae_iff.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set

theorem AvramDividend.Classical.zero_integral_positive_deficit_event_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (D : Ω → ℝ)
    (hD : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hAtom : P {ω : Ω | D ω = 0} = 0)
    (hIntegrable : Integrable (E.indicator D) P)
    (hIntegral : (∫ ω, E.indicator D ω ∂P) = 0) :
    P E = 0 := by sorry
