-- Prove2me | Theorems.Thm_ActuarialValuation_ruFiniteRuinBound_nonneg
-- name    : ActuarialValuation.ruFiniteRuinBound_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:28.393985+00:00
-- url     : https://prove2.me/theorems/cb78c147-2769-47ff-883e-031c2d6f7632
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruFiniteRuinBound_nonneg
-- statement:
--   The classical exponential ruin upper bound is strictly positive at finite parameters.
--
--   Mathematical relation:
--
--   $$
--   ruFiniteRuinBound\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruFiniteRuinBound

namespace ActuarialValuation

theorem ruFiniteRuinBound_nonneg (R u : ℝ) : 0<ruFiniteRuinBound R u := by sorry

end ActuarialValuation
