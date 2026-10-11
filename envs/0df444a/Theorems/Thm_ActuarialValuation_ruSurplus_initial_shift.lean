-- Prove2me | Theorems.Thm_ActuarialValuation_ruSurplus_initial_shift
-- name    : ActuarialValuation.ruSurplus_initial_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:36:09.276597+00:00
-- url     : https://prove2.me/theorems/0655dadd-4219-44a6-a9b5-b25e6eacd996
-- title:
--   Actuarial surplus and exponential supermartingale: ruSurplus_initial_shift
-- statement:
--   Increasing initial capital shifts every surplus path upwards by the same amount.
--
--   Mathematical relation:
--
--   $$
--   ruSurplus\_initial\_shift
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruSurplus

namespace ActuarialValuation

theorem ruSurplus_initial_shift {m : ℕ} (u v : ℝ) (G : ℕ → Fin m → ℝ) (k : ℕ) (ω : Fin m) : ruSurplus (u+v) G k ω = ruSurplus u G k ω + v := by sorry

end ActuarialValuation
