-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_mean
-- name    : ActuarialValuation.orderNeighbourSpread_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:27:22.931034+00:00
-- url     : https://prove2.me/theorems/2ccd4558-265f-41f4-8582-40e82d5bb783
-- title:
--   Symmetric interior spreading preserves expected aggregate loss
-- statement:
--   The increase in expected loss from moving δ/2 to c+1 exactly cancels the decrease from moving δ/2 to c−1. The mean therefore remains unchanged, even though the spread creates greater variability in the aggregate insurance claim.
--
--   **Mathematical statement**
--
--   $$
--   \mu_{w'}=\mu_w
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_mean is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMean

namespace ActuarialValuation

theorem orderNeighbourSpread_mean
  (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) :
  orderAggregateMean (orderNeighbourSpread w c delta) B =
    orderAggregateMean w B := by sorry

end ActuarialValuation
