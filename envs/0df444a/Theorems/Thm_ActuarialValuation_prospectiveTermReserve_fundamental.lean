-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_fundamental
-- name    : ActuarialValuation.prospectiveTermReserve_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:58:33.990976+00:00
-- url     : https://prove2.me/theorems/97659981-9f25-401a-9fa4-1d42bc5ab60d
-- title:
--   Fundamental conditional prospective reserve theorem
-- statement:
--   Combines positive survival normalisation, the decomposition of future loss and benefit-premium scaling.
--
--   **Mathematical statement**
--
--   $$
--   P(S_t)V_t=\mathbb E[L_{n,t}],\quad V_t=b\mathbb E[B_{n,t}\mid S_t]-\pi\mathbb E[Y_{n,t}\mid S_t]
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
import Definitions.Def_actuarial_futureTermBenefitPV
import Definitions.Def_actuarial_futureTermPremiumPV
import Definitions.Def_actuarial_futureTermLossPV
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_fundamental {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π c : ℝ) (hq : 0 < (P (valuationSurvivalEvent K t)).toReal)
    :
    ((P (valuationSurvivalEvent K t)).toReal *
      prospectiveTermReservePV P K v n t b π =
      ∫ ω, futureTermLossPV K v n t b π ω ∂P)
    ∧ (prospectiveTermReservePV P K v n t b π =
      b * (∫ ω, futureTermBenefitPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal -
      π * (∫ ω, futureTermPremiumPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal)
    ∧ (prospectiveTermReservePV P K v n t (c * b) (c * π) =
      c * prospectiveTermReservePV P K v n t b π) := by sorry

end ActuarialValuation
