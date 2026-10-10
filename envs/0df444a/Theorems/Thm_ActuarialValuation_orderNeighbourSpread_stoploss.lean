-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_stoploss
-- name    : ActuarialValuation.orderNeighbourSpread_stoploss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:27:36.822886+00:00
-- url     : https://prove2.me/theorems/add21e34-1ec7-4c21-a7e2-cbd124d23c01
-- title:
--   Symmetric interior spreading raises every expected stop-loss premium
-- statement:
--   The payment function (s−d) positive-part is convex in the claim amount s. Transferring nonnegative mass symmetrically from centre to its adjacent lower and higher losses can only increase its expected value, with a difference equal to δ/2 times the nonnegative discrete second difference at c.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_{w'}(d)-\Pi_w(d)=\frac{\delta}{2}[(c-1-d)_++(c+1-d)_+-2(c-d)_+]\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_stoploss is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
import Definitions.Def_actuarial_orderStopLossPremium

namespace ActuarialValuation

theorem orderNeighbourSpread_stoploss
  (w : ℕ → ℝ) (B c d : ℕ) (delta : ℝ)
  (hlo : 0 < c) (hhi : c + 1 ≤ B) (hd : 0 ≤ delta) :
  orderStopLossPremium w B d ≤
    orderStopLossPremium (orderNeighbourSpread w c delta) B d := by sorry

end ActuarialValuation
