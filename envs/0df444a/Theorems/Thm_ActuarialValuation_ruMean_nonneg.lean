-- Prove2me | Theorems.Thm_ActuarialValuation_ruMean_nonneg
-- name    : ActuarialValuation.ruMean_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:29.429869+00:00
-- url     : https://prove2.me/theorems/85f70322-0242-45c8-a7d4-e38fcd5e455d
-- title:
--   Finite probability martingales and bounded stopping: ruMean_nonneg
-- statement:
--   Expected nonnegative random insurance claims are nonnegative under nonnegative probability masses.
--
--   Mathematical relation:
--
--   $$
--   ruMean\_nonneg
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

theorem ruMean_nonneg {m : ℕ} (p : Fin m → ℝ) (X : Fin m → ℝ) (hp : ∀ ω, 0≤p ω) (hX : ∀ ω, 0≤X ω) : 0≤ruMean p X := by sorry

end ActuarialValuation
