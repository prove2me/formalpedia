-- Prove2me | Theorems.Thm_ActuarialValuation_orderStopLossPremium_nonneg
-- name    : ActuarialValuation.orderStopLossPremium_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:12.556004+00:00
-- url     : https://prove2.me/theorems/33797689-40ae-4b1d-8685-7a8c1f4a17ed
-- title:
--   Nonnegative masses produce nonnegative stop-loss expected payments
-- statement:
--   The amount of realised excess above an integer attachment is nonnegative. Under a nonnegative loss probability coefficient at every claim amount, each scenario's expected excess contribution is nonnegative, as is the finite sum.
--
--   **Mathematical statement**
--
--   $$
--   w_s\ge0\Rightarrow\Pi_w(d)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderStopLossPremium_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

theorem orderStopLossPremium_nonneg (w : ℕ → ℝ) (B d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ orderStopLossPremium w B d := by sorry

end ActuarialValuation
