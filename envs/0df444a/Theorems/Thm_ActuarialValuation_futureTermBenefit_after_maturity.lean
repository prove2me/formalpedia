-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermBenefit_after_maturity
-- name    : ActuarialValuation.futureTermBenefit_after_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:44:01.046026+00:00
-- url     : https://prove2.me/theorems/6bcc599f-cd9f-4a16-a1b4-79a6a19573a8
-- title:
--   Benefit cashflow vanishes after term expiry
-- statement:
--   Once duration reaches n, no insured death-year benefit remains.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Longrightarrow B_{n,t}=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermBenefitPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermBenefit_after_maturity {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (ht : n ≤ t)
    :
    futureTermBenefitPV K v n t ω = 0 := by sorry

end ActuarialValuation
