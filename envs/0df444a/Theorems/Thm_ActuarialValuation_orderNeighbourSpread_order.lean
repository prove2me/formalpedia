-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_order
-- name    : ActuarialValuation.orderNeighbourSpread_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:27:52.341888+00:00
-- url     : https://prove2.me/theorems/83c5d29d-964a-48d3-aada-947505714e78
-- title:
--   A one-step symmetric mean-preserving spread increases stop-loss risk
-- statement:
--   The result universally quantifies over the integer deductible and applies the convexity of each excess-payment function under an interior symmetric spread. It is the risk-ordering interpretation of the local probability transfer, without requiring nonnegative input coefficients for the algebraic difference identity.
--
--   **Mathematical statement**
--
--   $$
--   w\preceq_{\rm sl}w'
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_order is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderStopLossDominates
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

theorem orderNeighbourSpread_order
  (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) (hd : 0 ≤ delta) :
  orderStopLossDominates w (orderNeighbourSpread w c delta) B := by sorry

end ActuarialValuation
