-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponential_decreasing
-- name    : ActuarialValuation.ruExponential_decreasing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:05.922013+00:00
-- url     : https://prove2.me/theorems/8f0d0663-5ff1-43a6-bb83-de24e7038f5f
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponential_decreasing
-- statement:
--   For positive adjustment coefficient, larger capital gives no larger exponential risk transform.
--
--   Mathematical relation:
--
--   $$
--   ruExponential\_decreasing
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponential

namespace ActuarialValuation

theorem ruExponential_decreasing (R x y : ℝ) (hR : 0≤R) (hxy : x≤y) : ruExponential R y ≤ ruExponential R x := by sorry

end ActuarialValuation
