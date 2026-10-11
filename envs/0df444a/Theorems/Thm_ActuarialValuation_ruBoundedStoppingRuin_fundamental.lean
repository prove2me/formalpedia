-- Prove2me | Theorems.Thm_ActuarialValuation_ruBoundedStoppingRuin_fundamental
-- name    : ActuarialValuation.ruBoundedStoppingRuin_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:36.154406+00:00
-- url     : https://prove2.me/theorems/65f4d38b-adc9-4b83-ad71-d175696e6f2d
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruBoundedStoppingRuin_fundamental
-- statement:
--   The capstone derives an actual finite-horizon ruin probability upper bound from bounded stopped exponential-surplus nonpositive drift, normalised scenario probabilities, and the negative-capital ruin event, without assuming the ruin bound as a hypothesis.
--
--   Mathematical relation:
--
--   $$
--   ruBoundedStoppingRuin\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability
import Definitions.Def_actuarial_ruSurplus
import Definitions.Def_actuarial_ruFiniteRuinBound
import Definitions.Def_actuarial_ruStoppedIncrementMean
import Definitions.Def_actuarial_ruExponentialSurplus

namespace ActuarialValuation

theorem ruBoundedStoppingRuin_fundamental {m : ℕ} (p : Fin m → ℝ) (u R : ℝ) (G : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N) (hp : ∀ ω, 0≤p ω) (hn : (∑ ω : Fin m, p ω)=1) (hR : 0<R) (hinc : ∀ k ∈ Finset.range N, ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ k ≤ 0) : ruRuinProbability p (fun ω => ruSurplus u G (τ ω) ω < 0) ≤ ruFiniteRuinBound R u := by sorry

end ActuarialValuation
