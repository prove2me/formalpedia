-- Prove2me | Theorems.Thm_ActuarialValuation_ruExpectedStopped_telescope
-- name    : ActuarialValuation.ruExpectedStopped_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:32.544537+00:00
-- url     : https://prove2.me/theorems/f1166353-74b6-4c64-bc5d-c6504218a611
-- title:
--   Finite probability martingales and bounded stopping: ruExpectedStopped_telescope
-- statement:
--   Expected stopped process terminal value is initial expected value plus all stopped increments.
--
--   Mathematical relation:
--
--   $$
--   ruExpectedStopped\_telescope
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

theorem ruExpectedStopped_telescope {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) (N : ℕ) : ruExpectedStopped p X τ N = ruExpectedStopped p X τ 0 + ∑ k ∈ Finset.range N, ruStoppedIncrementMean p X τ k := by sorry

end ActuarialValuation
