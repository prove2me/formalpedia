-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermPremium_after_maturity
-- name    : ActuarialValuation.futureTermPremium_after_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:47:01.613922+00:00
-- url     : https://prove2.me/theorems/fed61acc-1d49-446d-8f90-4d7162941c36
-- title:
--   Premium cashflow vanishes after term expiry
-- statement:
--   No new premiums are payable at or after expiry of the finite-term contract.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Longrightarrow Y_{n,t}=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermPremiumPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermPremium_after_maturity {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (ht : n ≤ t)
    :
    futureTermPremiumPV K v n t ω = 0 := by sorry

end ActuarialValuation
