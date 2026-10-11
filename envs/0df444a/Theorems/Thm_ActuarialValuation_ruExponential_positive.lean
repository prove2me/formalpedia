-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponential_positive
-- name    : ActuarialValuation.ruExponential_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:23.526422+00:00
-- url     : https://prove2.me/theorems/c1f201fe-21e8-4664-850b-761916f9113e
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponential_positive
-- statement:
--   The exponential adjustment-coefficient transform is positive for finite real reserve.
--
--   Mathematical relation:
--
--   $$
--   ruExponential\_positive
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

theorem ruExponential_positive (R capital : ℝ) : 0 < ruExponential R capital := by sorry

end ActuarialValuation
