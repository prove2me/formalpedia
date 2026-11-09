-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
-- name    : AvramDividend.Classical.avram_ubv_jump11_past_event_integral_of_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:21:33.984554+00:00
-- url     : https://prove2.me/theorems/1820407b-4aa4-4b12-8c6c-df0e88cf6ae6
-- title:
--   A conditionally centred L1 martingale increment has zero expectation on every past event
-- statement:
--   For any integrable original-process martingale difference whose conditional expectation at the past sigma algebra is zero, its real integral restricted to any event measurable in that past is zero. This is the eventwise bridge needed to apply the Proved original Lévy-band L1 predictable compensator result c97f2b53 to the initial-filtration stochastic dividend inequality.
-- source:
--   UBV-JUMP11 crucial real eventwise cancellation for the original compensated finite-grid jump martingale.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_ubv_jump11_past_event_integral_of_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hMzero : P[M | m] =ᵐ[P] 0)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (∫ ω in A, M ω ∂P) = 0 := by sorry
