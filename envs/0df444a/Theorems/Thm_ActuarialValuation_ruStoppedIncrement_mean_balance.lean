-- Prove2me | Theorems.Thm_ActuarialValuation_ruStoppedIncrement_mean_balance
-- name    : ActuarialValuation.ruStoppedIncrement_mean_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:58.266305+00:00
-- url     : https://prove2.me/theorems/5866b4b7-9385-4372-aeb1-43ff12babf7a
-- title:
--   Finite probability martingales and bounded stopping: ruStoppedIncrement_mean_balance
-- statement:
--   Finite expected stopped process increments exactly reconcile consecutive expected values.
--
--   Mathematical relation:
--
--   $$
--   ruStoppedIncrement\_mean\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExpectedStopped
import Definitions.Def_actuarial_ruStoppedIncrementMean

namespace ActuarialValuation

theorem ruStoppedIncrement_mean_balance {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (k : ℕ) : ruExpectedStopped p X τ (k+1) = ruExpectedStopped p X τ k + ruStoppedIncrementMean p X τ k := by sorry

end ActuarialValuation
