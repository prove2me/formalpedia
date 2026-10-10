-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossPremium_above
-- name    : ActuarialValuation.orderStopLossPremium_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:24:56.107389+00:00
-- url     : https://prove2.me/theorems/8350dd64-a2ec-489c-b304-1a57ab140369
-- title:
--   Deductibles beyond the maximum loss have zero expected excess
-- statement:
--   Every possible aggregate claim amount in the finite grid is no greater than the deductible. Its natural-number excess payment is zero, so the net stop-loss premium vanishes regardless of the claim coefficients.
--
--   **Mathematical statement**
--
--   $$
--   d\ge B\Rightarrow\Pi_w(d)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossPremium_above is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

theorem orderStopLossPremium_above
  (w : ℕ → ℝ) (B d : ℕ) (h : B ≤ d) :
  orderStopLossPremium w B d = 0 := by sorry

end ActuarialValuation
