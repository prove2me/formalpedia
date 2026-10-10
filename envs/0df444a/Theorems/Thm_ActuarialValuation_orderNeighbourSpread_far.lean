-- Prove2me | Theorems.Thm_ActuarialValuation_orderNeighbourSpread_far
-- name    : ActuarialValuation.orderNeighbourSpread_far
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:26:26.178226+00:00
-- url     : https://prove2.me/theorems/6069c213-66ad-460c-9526-d48a1b7d6027
-- title:
--   An unaffected loss index retains its original probability coefficient
-- statement:
--   At an index other than the middle claim level or either adjacent level, every indicator controlling the symmetric transfer is false. The resulting scenario coefficient equals the original distribution's coefficient.
--
--   **Mathematical statement**
--
--   $$
--   s\notin\{c-1,c,c+1\}\Rightarrow w'_s=w_s
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 22, Section 22.4, printed page 409 (Library PDF page 435), parent framework: Definition 22.3 and equations (22.3)–(22.4). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://doi.org/10.1016/0167-6687(96)90002-5. The specific Lean declaration ActuarialValuation.orderNeighbourSpread_far is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread

namespace ActuarialValuation

theorem orderNeighbourSpread_far (w : ℕ → ℝ) (c s : ℕ) (delta : ℝ)
  (ha : s + 1 ≠ c) (hb : s ≠ c + 1) (hc : s ≠ c) :
  orderNeighbourSpread w c delta s = w s := by sorry

end ActuarialValuation
