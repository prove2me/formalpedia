-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponentialSurplus_recursion
-- name    : ActuarialValuation.ruExponentialSurplus_recursion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:38.714535+00:00
-- url     : https://prove2.me/theorems/7db2cea0-56ec-4322-ad20-79f3691f201a
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponentialSurplus_recursion
-- statement:
--   Exponential reserve updates by multiplying the transform of each realised increment.
--
--   Mathematical relation:
--
--   $$
--   ruExponentialSurplus\_recursion
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponentialSurplus
import Definitions.Def_actuarial_ruExponential

namespace ActuarialValuation

theorem ruExponentialSurplus_recursion {m : ℕ} (u R : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) : ruExponentialSurplus u R G (k+1) ω = ruExponentialSurplus u R G k ω * ruExponential R (G k ω) := by sorry

end ActuarialValuation
