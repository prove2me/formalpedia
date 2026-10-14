-- Prove2me | Theorems.Thm_ActuarialValuation_ruStoppedIncrement_after_horizon
-- name    : ActuarialValuation.ruStoppedIncrement_after_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:17.824042+00:00
-- url     : https://prove2.me/theorems/f23d9606-0128-4e0a-9c1c-8f7805a1314c
-- title:
--   Finite probability martingales and bounded stopping: ruStoppedIncrement_after_horizon
-- statement:
--   A bounded stopping time produces zero stopped-process increments after the global terminal horizon.
--
--   Mathematical relation:
--
--   $$
--   ruStoppedIncrement\_after\_horizon
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruStoppedIncrementMean

namespace ActuarialValuation

theorem ruStoppedIncrement_after_horizon {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (N k : ℕ) (hτ : ∀ ω, τ ω≤N) (hk : N≤k) : ruStoppedIncrementMean p X τ k = 0 := by sorry

end ActuarialValuation
