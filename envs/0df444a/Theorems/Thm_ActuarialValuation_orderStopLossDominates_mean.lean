-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossDominates_mean
-- name    : ActuarialValuation.orderStopLossDominates_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:26:08.910984+00:00
-- url     : https://prove2.me/theorems/b6005fed-6493-4d3e-aaa2-a2dc12978618
-- title:
--   Stop-loss order implies no greater aggregate expected loss
-- statement:
--   The stop-loss comparison is assumed at every attachment including deductible zero. At zero deductible, stop-loss expected payment equals aggregate expected loss, so the first risk's gross mean is no greater than the second's.
--
--   **Mathematical statement**
--
--   $$
--   f\preceq_{\rm sl}g\Rightarrow \mu_f\le\mu_g
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossDominates_mean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates
import Definitions.Def_actuarial_orderAggregateMean
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

theorem orderStopLossDominates_mean
  (f g : ℕ → ℝ) (B : ℕ)
  (h : orderStopLossDominates f g B) :
  orderAggregateMean f B ≤ orderAggregateMean g B := by sorry

end ActuarialValuation
