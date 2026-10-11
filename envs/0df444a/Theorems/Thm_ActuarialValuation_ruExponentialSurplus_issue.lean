-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponentialSurplus_issue
-- name    : ActuarialValuation.ruExponentialSurplus_issue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:25.541221+00:00
-- url     : https://prove2.me/theorems/f415e61b-c651-41d6-a7dd-ff386a0407fa
-- title:
--   Actuarial surplus and exponential supermartingale: ruExponentialSurplus_issue
-- statement:
--   The issue-time transformed surplus is a deterministic initial value, independent of future scenarios.
--
--   Mathematical relation:
--
--   $$
--   ruExponentialSurplus\_issue
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

theorem ruExponentialSurplus_issue {m : ℕ} (u R : ℝ) (G : ℕ → Fin m → ℝ) (ω : Fin m) : ruExponentialSurplus u R G 0 ω = ruExponential R u := by sorry

end ActuarialValuation
