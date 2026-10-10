-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_mass
-- name    : ActuarialValuation.orderNeighbourSpread_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:27:00.2885+00:00
-- url     : https://prove2.me/theorems/841772ec-3355-415f-ad67-0b966de5d782
-- title:
--   Symmetric interior spreading preserves total aggregate probability mass
-- statement:
--   Both adjacent loss levels lie within the bounded grid because the centre is strictly positive and centre+1 is no greater than B. The transfer removes δ at the centre and adds δ/2 at each neighbour, leaving the total probability mass unchanged.
--
--   **Mathematical statement**
--
--   $$
--   M_{w'}=M_w
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_mass is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMass

namespace ActuarialValuation

theorem orderNeighbourSpread_mass
  (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) :
  orderAggregateMass (orderNeighbourSpread w c delta) B =
    orderAggregateMass w B := by sorry

end ActuarialValuation
