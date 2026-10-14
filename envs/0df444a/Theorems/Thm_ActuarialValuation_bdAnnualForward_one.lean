-- Prove2me | Theorems.Thm_ActuarialValuation_bdAnnualForward_one
-- name    : ActuarialValuation.bdAnnualForward_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:35:16.013371+00:00
-- url     : https://prove2.me/theorems/bcd3c8c7-0365-4b96-8c6a-e3e21c8aac70
-- title:
--   Deterministic zero-coupon bonds and forward discounts: bdAnnualForward_one
-- statement:
--   One-year forward rate equals gross single-period forward return minus one.
--
--   Mathematical relation:
--
--   $$
--   bdAnnualForward\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdAnnualForward
import Definitions.Def_actuarial_bdForwardGross

namespace ActuarialValuation

theorem bdAnnualForward_one (D : ℕ → ℝ) (t : ℕ) : bdAnnualForward D t = bdForwardGross D t (t+1)-1 := by sorry

end ActuarialValuation
