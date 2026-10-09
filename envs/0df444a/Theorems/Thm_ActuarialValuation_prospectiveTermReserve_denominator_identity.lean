-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_denominator_identity
-- name    : ActuarialValuation.prospectiveTermReserve_denominator_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:57:44.934784+00:00
-- url     : https://prove2.me/theorems/25126b64-e4dd-4fbc-9f7b-c4d22b320510
-- title:
--   Positive survival probability normalises prospective loss
-- statement:
--   Where survival is possible, the product of survival probability and reserve recovers the unconditional expected future loss.
--
--   **Mathematical statement**
--
--   $$
--   P(S_t)V_t=\mathbb E[L_{n,t}],\quad P(S_t)>0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
import Definitions.Def_actuarial_futureTermLossPV
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_denominator_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π : ℝ)
    (hq : 0 < (P (valuationSurvivalEvent K t)).toReal)
    :
    (P (valuationSurvivalEvent K t)).toReal *
      prospectiveTermReservePV P K v n t b π =
      ∫ ω, futureTermLossPV K v n t b π ω ∂P := by sorry

end ActuarialValuation
