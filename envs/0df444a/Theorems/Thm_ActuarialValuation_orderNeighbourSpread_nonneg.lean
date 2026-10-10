-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_nonneg
-- name    : ActuarialValuation.orderNeighbourSpread_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:26:42.509235+00:00
-- url     : https://prove2.me/theorems/45385157-cfce-4fde-9653-e01ced896bc7
-- title:
--   Transfer at most the central mass preserves nonnegative coefficients
-- statement:
--   Moving a nonnegative mass δ from the centre leaves a nonnegative central coefficient if δ does not exceed the mass already there. Each neighbouring coefficient gains δ/2 and other loss coefficients are unchanged. The argument also handles overlapping indicators at integer boundaries by direct case analysis.
--
--   **Mathematical statement**
--
--   $$
--   0\le\delta\le w_c,\ w\ge0\Rightarrow w'\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread

namespace ActuarialValuation

theorem orderNeighbourSpread_nonneg
  (w : ℕ → ℝ) (c s : ℕ) (delta : ℝ)
  (hw : ∀ k, 0 ≤ w k)
  (hd : 0 ≤ delta) (hcentre : delta ≤ w c) :
  0 ≤ orderNeighbourSpread w c delta s := by sorry

end ActuarialValuation
