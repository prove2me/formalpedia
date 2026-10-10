-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossDominates_refl
-- name    : ActuarialValuation.orderStopLossDominates_refl
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:28.31165+00:00
-- url     : https://prove2.me/theorems/7fccea33-0053-48eb-94c5-007cba37f3c1
-- title:
--   Every discrete loss model dominates itself in stop-loss order
-- statement:
--   The stop-loss order compares identical expected excess payments at each deductible when both claim coefficient arrays are the same. Equality is reflexive and does not depend on nonnegative masses or normalisation.
--
--   **Mathematical statement**
--
--   $$
--   w\preceq_{\rm sl}w
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossDominates_refl is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossDominates

namespace ActuarialValuation

theorem orderStopLossDominates_refl (w : ℕ → ℝ) (B : ℕ) :
  orderStopLossDominates w w B := by sorry

end ActuarialValuation
