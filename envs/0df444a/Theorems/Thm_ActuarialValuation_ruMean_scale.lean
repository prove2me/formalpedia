-- Prove2me | Theorems.Thm_ActuarialValuation_ruMean_scale
-- name    : ActuarialValuation.ruMean_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:32:11.062343+00:00
-- url     : https://prove2.me/theorems/58fb383a-702c-4ab1-9c53-d6fb5fef93e1
-- title:
--   Finite probability martingales and bounded stopping: ruMean_scale
-- statement:
--   Expected cashflow scales linearly in a monetary amount.
--
--   Mathematical relation:
--
--   $$
--   ruMean\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 18 and 23, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://ocw.mit.edu/courses/18-440-probability-and-random-variables-spring-2014/resources/mit18_440s14_lecture35/. The proposed model is rooted in Promislow chapter 18 and 23. The target Lean identity is an original derivation, not a verbatim published result. Published source page 426 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean

namespace ActuarialValuation

theorem ruMean_scale {m : ℕ} (p : Fin m → ℝ) (X : Fin m → ℝ) (a : ℝ) : ruMean p (fun ω => a*X ω) = a*ruMean p X := by sorry

end ActuarialValuation
