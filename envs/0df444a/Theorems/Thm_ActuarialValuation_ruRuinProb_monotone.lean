-- Prove2me | Theorems.Thm_ActuarialValuation_ruRuinProb_monotone
-- name    : ActuarialValuation.ruRuinProb_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:00.929195+00:00
-- url     : https://prove2.me/theorems/9d2b8e9e-9396-47c0-86f6-8b29aa12f4e7
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruRuinProb_monotone
-- statement:
--   Enlarging the scenario ruin event cannot reduce its probability.
--
--   Mathematical relation:
--
--   $$
--   ruRuinProb\_monotone
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability

namespace ActuarialValuation

theorem ruRuinProb_monotone {m : ℕ} (p : Fin m → ℝ) (A B : Fin m → Prop) [DecidablePred A] [DecidablePred B] (hp : ∀ ω, 0≤p ω) (hAB : ∀ ω, A ω → B ω) : ruRuinProbability p A ≤ ruRuinProbability p B := by sorry

end ActuarialValuation
