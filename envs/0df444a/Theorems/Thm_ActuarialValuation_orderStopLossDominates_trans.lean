-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossDominates_trans
-- name    : ActuarialValuation.orderStopLossDominates_trans
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:48.715092+00:00
-- url     : https://prove2.me/theorems/55e477cd-c2c4-4dd6-b955-d8ea9f472cb6
-- title:
--   Stop-loss order is transitive
-- statement:
--   If the first risk's expected excess is no greater than the second's at every deductible, and the second is likewise below the third, comparing their real-valued premiums gives the first below the third for every deductible.
--
--   **Mathematical statement**
--
--   $$
--   f\preceq_{\rm sl}g,\ g\preceq_{\rm sl}h\Rightarrow f\preceq_{\rm sl}h
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossDominates_trans is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates

namespace ActuarialValuation

theorem orderStopLossDominates_trans
  (f g h : ℕ → ℝ) (B : ℕ)
  (hfg : orderStopLossDominates f g B)
  (hgh : orderStopLossDominates g h B) :
  orderStopLossDominates f h B := by sorry

end ActuarialValuation
