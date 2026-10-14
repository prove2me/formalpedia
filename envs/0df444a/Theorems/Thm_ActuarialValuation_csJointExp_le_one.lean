-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_le_one
-- name    : ActuarialValuation.csJointExp_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:55.309893+00:00
-- url     : https://prove2.me/theorems/cac5cfb6-8b5e-4f3a-ba7a-11cda41d1faf
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_le_one
-- statement:
--   Under nonnegative primitive rates and horizons, joint survival cannot exceed one.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_le\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointExp

namespace ActuarialValuation

theorem csJointExp_le_one (a b c s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) : csJointExp a b c s t ≤ 1 := by sorry

end ActuarialValuation
