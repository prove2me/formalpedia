-- Prove2me | Theorems.Thm_ActuarialValuation_ruBoundedRuinSupermartingale
-- name    : ActuarialValuation.ruBoundedRuinSupermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:14.977693+00:00
-- url     : https://prove2.me/theorems/412e1572-6635-4f63-bce5-1c6e947d1110
-- title:
--   Ruin events and finite-horizon Lundberg bound: ruBoundedRuinSupermartingale
-- statement:
--   A bounded stopping time and nonpositive expected increments of the exponential surplus process yield the terminal Lundberg transform bound.
--
--   Mathematical relation:
--
--   $$
--   ruBoundedRuinSupermartingale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruStoppedIncrementMean
import Definitions.Def_actuarial_ruExponentialSurplus
import Definitions.Def_actuarial_ruTerminalExponentialMean
import Definitions.Def_actuarial_ruSurplus
import Definitions.Def_actuarial_ruFiniteRuinBound

namespace ActuarialValuation

theorem ruBoundedRuinSupermartingale {m : ℕ} (p : Fin m → ℝ) (u R : ℝ) (G : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N) (hn : (∑ ω : Fin m, p ω)=1) (hinc : ∀ k ∈ Finset.range N, ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ k ≤ 0) : ruTerminalExponentialMean p R (fun ω => ruSurplus u G (τ ω) ω) ≤ ruFiniteRuinBound R u := by sorry

end ActuarialValuation
