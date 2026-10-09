-- Prove2me | Theorems.Thm_ActuarialValuation_valuationSurvivalEvent_zero
-- name    : ActuarialValuation.valuationSurvivalEvent_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:39:36.263691+00:00
-- url     : https://prove2.me/theorems/4e1f290e-7a0f-453f-92d2-86cb9e705c43
-- title:
--   Every life is in force at inception
-- statement:
--   Nonnegative natural-valued curtate lifetime makes the time-zero survival event certain.
--
--   **Mathematical statement**
--
--   $$
--   S_0=\Omega
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
open MeasureTheory

namespace ActuarialValuation

theorem valuationSurvivalEvent_zero {Ω : Type*} (K : Ω → ℕ)
    :
    valuationSurvivalEvent K 0 = Set.univ := by sorry

end ActuarialValuation
