-- Prove2me | Theorems.Thm_ActuarialValuation_bdZeroPrice_nonneg
-- name    : ActuarialValuation.bdZeroPrice_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:35.900518+00:00
-- url     : https://prove2.me/theorems/d62ab649-b6c3-4054-8880-ac3aafcdcfbf
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdZeroPrice_nonneg
-- statement:
--   Nonnegative redemption and discount yield nonnegative current bond price.
--
--   Mathematical relation:
--
--   $$
--   bdZeroPrice\_nonneg
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

theorem bdZeroPrice_nonneg (D : ℕ → ℝ) (face : ℝ) (t : ℕ) (hf : 0≤face) (hD : 0≤D t) : 0≤bdZeroPrice D face t := by sorry

end ActuarialValuation
