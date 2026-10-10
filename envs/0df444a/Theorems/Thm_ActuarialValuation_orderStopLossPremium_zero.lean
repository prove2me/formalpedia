-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossPremium_zero
-- name    : ActuarialValuation.orderStopLossPremium_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:24:40.359913+00:00
-- url     : https://prove2.me/theorems/64b6405c-8b08-4852-a41b-652f50327bac
-- title:
--   A zero deductible transfers all aggregate losses
-- statement:
--   Since every nonnegative integer loss exceeds or equals attachment zero, the stop-loss payment equals the gross loss in each scenario. Thus the expected excess premium at attachment zero coincides exactly with the original aggregate expected claim.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_w(0)=\mu_w
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossPremium_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium
import Definitions.Def_actuarial_orderAggregateMean

namespace ActuarialValuation

theorem orderStopLossPremium_zero (w : ℕ → ℝ) (B : ℕ) :
  orderStopLossPremium w B 0 = orderAggregateMean w B := by sorry

end ActuarialValuation
