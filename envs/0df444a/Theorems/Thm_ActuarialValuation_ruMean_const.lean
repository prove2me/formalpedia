-- Prove2me | Theorems.Thm_ActuarialValuation_ruMean_const
-- name    : ActuarialValuation.ruMean_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:41.364044+00:00
-- url     : https://prove2.me/theorems/8340671d-d8bd-4761-bf8e-672a34d2bd16
-- title:
--   Finite probability martingales and bounded stopping: ruMean_const
-- statement:
--   Normalised finite probabilities preserve the constant value under expectation.
--
--   Mathematical relation:
--
--   $$
--   ruMean\_const
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

theorem ruMean_const {m : ℕ} (p : Fin m → ℝ) (x : ℝ) (hp : (∑ ω : Fin m, p ω)=1) : ruMean p (fun _ => x) = x := by sorry

end ActuarialValuation
