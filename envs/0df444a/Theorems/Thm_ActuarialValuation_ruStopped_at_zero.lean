-- Prove2me | Theorems.Thm_ActuarialValuation_ruStopped_at_zero
-- name    : ActuarialValuation.ruStopped_at_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:32:48.439338+00:00
-- url     : https://prove2.me/theorems/ff0cb15e-955e-45bb-901b-b5a77bd0b6e1
-- title:
--   Finite probability martingales and bounded stopping: ruStopped_at_zero
-- statement:
--   The stopped process starts at the unstopped issue-time value.
--
--   Mathematical relation:
--
--   $$
--   ruStopped\_at\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruStopped

namespace ActuarialValuation

theorem ruStopped_at_zero {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (ω : Fin m) : ruStopped X τ 0 ω = X 0 ω := by sorry

end ActuarialValuation
