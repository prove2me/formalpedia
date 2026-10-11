-- Prove2me | Theorems.Thm_ActuarialValuation_csJointSurvival_antitone_left
-- name    : ActuarialValuation.csJointSurvival_antitone_left
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:32:18.591028+00:00
-- url     : https://prove2.me/theorems/d7781405-b15a-475e-8c0b-da5a154bfbac
-- title:
--   Actual joint-lifetime events and cause partition: csJointSurvival_antitone_left
-- statement:
--   Raising the first survivor threshold cannot enlarge the measured event.
--
--   Mathematical relation:
--
--   $$
--   csJointSurvival\_antitone\_left
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointSurvival

namespace ActuarialValuation

theorem csJointSurvival_antitone_left {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (s1 s2 t : ℝ) (h : s1 ≤ s2) : csJointSurvival μ U V Z s2 t ≤ csJointSurvival μ U V Z s1 t := by sorry

end ActuarialValuation
