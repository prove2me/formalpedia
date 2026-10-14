-- Prove2me | Theorems.Thm_ActuarialValuation_ruExponentialRuinEventBound
-- name    : ActuarialValuation.ruExponentialRuinEventBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:58.576974+00:00
-- url     : https://prove2.me/theorems/2395481a-8cc8-42b9-9fbb-59353e29a4e5
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruExponentialRuinEventBound
-- statement:
--   On every ruined path exponential transformed reserve exceeds one, so the ruin event indicator is dominated by the exponential random variable.
--
--   Mathematical relation:
--
--   $$
--   ruExponentialRuinEventBound
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability
import Definitions.Def_actuarial_ruTerminalExponentialMean

namespace ActuarialValuation

theorem ruExponentialRuinEventBound {m : ℕ} (p : Fin m → ℝ) (terminal : Fin m → ℝ) (R : ℝ) (hp : ∀ ω, 0≤p ω) (hR : 0<R) : ruRuinProbability p (fun ω => terminal ω < 0) ≤ ruTerminalExponentialMean p R terminal := by sorry

end ActuarialValuation
