-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponential_factor
-- name    : ActuarialValuation.ruExponential_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:36:52.274265+00:00
-- url     : https://prove2.me/theorems/41543d40-fbeb-4652-8f53-8dba3a5adba8
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponential_factor
-- statement:
--   The exponential transform factors across initial reserve and realised net premium-minus-claim increments.
--
--   Mathematical relation:
--
--   $$
--   ruExponential\_factor
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

theorem ruExponential_factor (R x y : ℝ) : ruExponential R (x+y) = ruExponential R x * ruExponential R y := by sorry

end ActuarialValuation
