-- Prove2me | Theorems.Thm_ActuarialValuation_bdFlatDiscount_succ
-- name    : ActuarialValuation.bdFlatDiscount_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:46.170506+00:00
-- url     : https://prove2.me/theorems/08ab890b-102d-48d0-9efa-d6f5a5a4b15e
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdFlatDiscount_succ
-- statement:
--   One more year of flat gross-rate discounting multiplies the discount by its reciprocal.
--
--   Mathematical relation:
--
--   $$
--   bdFlatDiscount\_succ
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdFlatDiscount

namespace ActuarialValuation

theorem bdFlatDiscount_succ (R : ℝ) (t : ℕ) (h : R ≠ 0) : bdFlatDiscount R (t+1) * R = bdFlatDiscount R t := by sorry

end ActuarialValuation
