-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_fundamental
-- name    : ActuarialValuation.orderNeighbourSpread_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:28:11.942975+00:00
-- url     : https://prove2.me/theorems/86ab0da2-a939-41d8-92ff-86ba348edc75
-- title:
--   Finite mean-preserving spread conserves mass and mean but increases stop-loss risk
-- statement:
--   The capstone shows that a feasible symmetric probability transfer to adjacent losses produces a valid nonnegative bounded coefficient distribution, preserves the aggregate total probability and mean, yet weakly raises every stop-loss expected excess premium. This is an explicit constructive mean-preserving spread and a finite-lattice convex-order result.
--
--   **Mathematical statement**
--
--   $$
--   w'\ge0,\ M_{w'}=M_w,\ \mu_{w'}=\mu_w,\ w\preceq_{\rm sl}w'
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderAggregateMass
import Definitions.Def_actuarial_orderAggregateMean
import Definitions.Def_actuarial_orderStopLossDominates

namespace ActuarialValuation

theorem orderNeighbourSpread_fundamental
  (w : ℕ → ℝ) (B c : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B)
  (hw : ∀ s, 0 ≤ w s) (hd : 0 ≤ delta) (hcap : delta ≤ w c) :
  (∀ s, 0 ≤ orderNeighbourSpread w c delta s) ∧
  (orderAggregateMass (orderNeighbourSpread w c delta) B =
    orderAggregateMass w B) ∧
  (orderAggregateMean (orderNeighbourSpread w c delta) B =
    orderAggregateMean w B) ∧
  orderStopLossDominates w (orderNeighbourSpread w c delta) B := by sorry

end ActuarialValuation
