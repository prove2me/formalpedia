-- Prove2me | Theorems.Thm_ActuarialValuation_ruExpectedStopped_initial
-- name    : ActuarialValuation.ruExpectedStopped_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:40.883346+00:00
-- url     : https://prove2.me/theorems/3f1428bb-ce6d-4186-b79f-a13e65dd6d88
-- title:
--   Finite probability martingales and bounded stopping: ruExpectedStopped_initial
-- statement:
--   Expected stopped capital at issue is the expected original process at issue.
--
--   Mathematical relation:
--
--   $$
--   ruExpectedStopped\_initial
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExpectedStopped
import Definitions.Def_actuarial_ruMean

namespace ActuarialValuation

theorem ruExpectedStopped_initial {m : ℕ} (p : Fin m → ℝ) (X : ℕ → Fin m → ℝ) (τ : Fin m → ℕ) : ruExpectedStopped p X τ 0 = ruMean p (X 0) := by sorry

end ActuarialValuation
