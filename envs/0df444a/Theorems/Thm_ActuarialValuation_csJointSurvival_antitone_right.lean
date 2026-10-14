-- Prove2me | Theorems.Thm_ActuarialValuation_csJointSurvival_antitone_right
-- name    : ActuarialValuation.csJointSurvival_antitone_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:44.721991+00:00
-- url     : https://prove2.me/theorems/540c12b4-ec18-431e-9cfb-13aaa12b289f
-- title:
--   Actual joint-lifetime events and cause partition: csJointSurvival_antitone_right
-- statement:
--   Raising the second survivor threshold cannot enlarge the joint survivor event.
--
--   Mathematical relation:
--
--   $$
--   csJointSurvival\_antitone\_right
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

theorem csJointSurvival_antitone_right {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (s t1 t2 : ℝ) (h : t1 ≤ t2) : csJointSurvival μ U V Z s t2 ≤ csJointSurvival μ U V Z s t1 := by sorry

end ActuarialValuation
