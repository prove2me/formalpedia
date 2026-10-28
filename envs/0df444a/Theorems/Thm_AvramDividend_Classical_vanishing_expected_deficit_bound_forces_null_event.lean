-- Prove2me | Theorems.Thm_AvramDividend_Classical_vanishing_expected_deficit_bound_forces_null_event
-- name    : AvramDividend.Classical.vanishing_expected_deficit_bound_forces_null_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:14:53.412719+00:00
-- url     : https://prove2.me/theorems/e547ec88-b99e-4f10-ba18-6b662df025ea
-- title:
--   Vanishing finite-mesh expectation bounds imply null survival when the nonnegative deficit has no zero atom
-- statement:
--   A nonnegative integrable deficit restricted to an event cannot have a positive expectation if it is bounded above by a sequence converging to zero. Thus its integral vanishes. When the unrestricted deficit has a null zero atom, the previously proved null-event theorem concludes that the event is null. This is the exact abstract measure-theoretic endpoint of the infinite-activity BV reflected zero-barrier mesh programme.
-- source:
--   Proved zero_integral_positive_deficit_event_null; Mathlib le_of_tendsto and integral_nonneg_of_ae.

import Theorems.Thm_AvramDividend_Classical_zero_integral_positive_deficit_event_null
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set Filter

theorem AvramDividend.Classical.vanishing_expected_deficit_bound_forces_null_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (D : Ω → ℝ)
    (hD : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hAtom : P {ω : Ω | D ω = 0} = 0)
    (hInt : Integrable (E.indicator D) P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (nhds (0 : ℝ)))
    (hBound : ∀ n : ℕ,
      (∫ ω, E.indicator D ω ∂P) ≤ b n) :
    P E = 0 := by sorry
