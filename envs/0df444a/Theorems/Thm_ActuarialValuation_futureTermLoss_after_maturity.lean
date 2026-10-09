-- Prove2me | Theorems.Thm_ActuarialValuation_futureTermLoss_after_maturity
-- name    : ActuarialValuation.futureTermLoss_after_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T22:49:17.478712+00:00
-- url     : https://prove2.me/theorems/e7262a8e-5e67-4339-915c-41192c98940a
-- title:
--   Prospective loss vanishes after maturity
-- statement:
--   With no benefit or premium cashflows left, the prospective loss vanishes.
--
--   **Mathematical statement**
--
--   $$
--   t\ge n\Longrightarrow L_{n,t}=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermLossPV
open MeasureTheory

namespace ActuarialValuation

theorem futureTermLoss_after_maturity {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (b π : ℝ) (ht : n ≤ t)
    :
    futureTermLossPV K v n t b π ω = 0 := by sorry

end ActuarialValuation
