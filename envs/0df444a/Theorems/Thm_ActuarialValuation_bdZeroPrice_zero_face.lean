-- Prove2me | Theorems.Thm_ActuarialValuation_bdZeroPrice_zero_face
-- name    : ActuarialValuation.bdZeroPrice_zero_face
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:02.100427+00:00
-- url     : https://prove2.me/theorems/21362dfe-a47d-4b70-aa9e-06db21d3f76d
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdZeroPrice_zero_face
-- statement:
--   A bond with zero redemption amount has zero value.
--
--   Mathematical relation:
--
--   $$
--   bdZeroPrice\_zero\_face
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdZeroPrice

namespace ActuarialValuation

theorem bdZeroPrice_zero_face (D : ℕ → ℝ) (t : ℕ) : bdZeroPrice D 0 t = 0 := by sorry

end ActuarialValuation
