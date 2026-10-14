-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinCapital_monotone
-- name    : ActuarialValuation.ruRuinCapital_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:34.20898+00:00
-- url     : https://prove2.me/theorems/3076426a-f507-4a4c-8f4c-d9323320cdd1
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinCapital_monotone
-- statement:
--   An insurer with more starting capital cannot be ruined on a path unless one with less capital is also ruined.
--
--   Mathematical relation:
--
--   $$
--   ruRuinCapital\_monotone
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinAtHorizon
import Definitions.Def_actuarial_ruSurplus

namespace ActuarialValuation

theorem ruRuinCapital_monotone {m : ℕ} (u v : ℝ) (G : ℕ → Fin m → ℝ) (N : ℕ) (huv : u≤v) (ω : Fin m) : ruRuinAtHorizon v G N ω → ruRuinAtHorizon u G N ω := by sorry

end ActuarialValuation
