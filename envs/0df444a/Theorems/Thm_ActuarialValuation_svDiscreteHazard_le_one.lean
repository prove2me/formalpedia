-- Prove2me | Theorems.Thm_ActuarialValuation_svDiscreteHazard_le_one
-- name    : ActuarialValuation.svDiscreteHazard_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:55.525978+00:00
-- url     : https://prove2.me/theorems/b8216037-e756-45f1-9900-efba65682b5b
-- title:
--   Measurable lifetime distributions and conditional survival: svDiscreteHazard_le_one
-- statement:
--   Discrete failure conditional probability is at most one because integer failure is contained in the corresponding at-risk population.
--
--   Mathematical relation:
--
--   $$
--   svDiscreteHazard\_le\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svDiscreteHazard
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svFailureMass

namespace ActuarialValuation

theorem svDiscreteHazard_le_one (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k) (hs : svSurvival μ T ((k:ℝ)-1) ≠ 0) : svDiscreteHazard μ T k ≤ 1 := by sorry

end ActuarialValuation
