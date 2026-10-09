-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermBenefit_nonnegative
-- name    : ActuarialValuation.futureTermBenefit_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:49:48.76191+00:00
-- url     : https://prove2.me/theorems/456970a0-1124-4e8f-b533-11a95c37cafe
-- title:
--   Future benefit has nonnegative PV
-- statement:
--   Death benefit PV is nonnegative for a nonnegative discount factor.
--
--   **Mathematical statement**
--
--   $$
--   v\ge0\Longrightarrow B_{n,t}\ge0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermBenefitPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermBenefit_nonnegative {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (hv : 0 ≤ v)
    :
    0 ≤ futureTermBenefitPV K v n t ω := by sorry

end ActuarialValuation
