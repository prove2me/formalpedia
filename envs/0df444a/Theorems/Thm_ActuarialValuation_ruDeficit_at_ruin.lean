-- Prove2me | Theorems.Thm_ActuarialValuation_ruDeficit_at_ruin
-- name    : ActuarialValuation.ruDeficit_at_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:11.774352+00:00
-- url     : https://prove2.me/theorems/49fb92af-a8d1-414c-8c81-f392e95a598e
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruDeficit_at_ruin
-- statement:
--   A negative terminal reserve has a positive deficit equal to its absolute shortfall.
--
--   Mathematical relation:
--
--   $$
--   ruDeficit\_at\_ruin
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinDeficit

namespace ActuarialValuation

theorem ruDeficit_at_ruin (capital : ℝ) (h : capital<0) : ruRuinDeficit capital = -capital := by sorry

end ActuarialValuation
