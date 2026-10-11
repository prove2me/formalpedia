-- Prove2me | Theorems.Thm_ActuarialValuation_ruStopped_past_stop
-- name    : ActuarialValuation.ruStopped_past_stop
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:06.064045+00:00
-- url     : https://prove2.me/theorems/ed0f853c-9135-4f67-b3b2-ffd78b197d3c
-- title:
--   Finite probability martingales and bounded stopping: ruStopped_past_stop
-- statement:
--   A stopped process is frozen after its individual stopping time.
--
--   Mathematical relation:
--
--   $$
--   ruStopped\_past\_stop
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

theorem ruStopped_past_stop {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (k : ℕ) (ω : Fin m) (hτ : τ ω≤k) : ruStopped X τ k ω = X (τ ω) ω := by sorry

end ActuarialValuation
