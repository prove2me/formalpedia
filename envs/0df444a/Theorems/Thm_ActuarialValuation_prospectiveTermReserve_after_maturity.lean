-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_after_maturity
-- name    : ActuarialValuation.prospectiveTermReserve_after_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:54:40.620976+00:00
-- url     : https://prove2.me/theorems/ae1ba54a-3464-4adc-b518-b448a5563406
-- title:
--   Reserve is zero after term expiry
-- statement:
--   Future loss vanishes after term expiry, with this formal quotient returning zero even if the in-force event has zero probability.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Longrightarrow V_t=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_after_maturity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π : ℝ) (ht : n ≤ t)
    :
    prospectiveTermReservePV P K v n t b π = 0 := by sorry

end ActuarialValuation
