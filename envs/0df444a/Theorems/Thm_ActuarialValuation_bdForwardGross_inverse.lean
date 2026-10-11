-- Prove2me | Theorems.Thm_ActuarialValuation_bdForwardGross_inverse
-- name    : ActuarialValuation.bdForwardGross_inverse
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:27.738163+00:00
-- url     : https://prove2.me/theorems/4050997e-d2c1-4654-a057-1714a09c8bdd
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdForwardGross_inverse
-- statement:
--   The forward gross accumulation factor is the reciprocal of the forward discount when both spot prices are nonzero.
--
--   Mathematical relation:
--
--   $$
--   bdForwardGross\_inverse
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardGross
import Definitions.Def_actuarial_bdForwardDiscount

namespace ActuarialValuation

theorem bdForwardGross_inverse (D : ℕ → ℝ) (s t : ℕ) (hs : D s ≠ 0) (ht : D t ≠ 0) : bdForwardGross D s t * bdForwardDiscount D s t = 1 := by sorry

end ActuarialValuation
