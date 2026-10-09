-- Prove2me | Theorems.Thm_ActuarialValuation_prospectiveTermReserve_decomposition
-- name    : ActuarialValuation.prospectiveTermReserve_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:55:52.207611+00:00
-- url     : https://prove2.me/theorems/733806a9-d2e6-4e55-a5bf-78efc69cc990
-- title:
--   Reserve splits into expected benefit less premiums
-- statement:
--   Linearity splits the prospective reserve into benefit outgo and future premium income with a common survival denominator.
--
--   **Mathematical statement**
--
--   $$
--   V_t=b\,\mathbb E[B_{n,t}\mid S_t]-\pi\,\mathbb E[Y_{n,t}\mid S_t]
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
import Definitions.Def_actuarial_futureTermBenefitPV
import Definitions.Def_actuarial_futureTermPremiumPV
import Definitions.Def_actuarial_prospectiveTermReservePV
open MeasureTheory

namespace ActuarialValuation

theorem prospectiveTermReserve_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π : ℝ)
    :
    prospectiveTermReservePV P K v n t b π =
      b * (∫ ω, futureTermBenefitPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal -
      π * (∫ ω, futureTermPremiumPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal := by sorry

end ActuarialValuation
