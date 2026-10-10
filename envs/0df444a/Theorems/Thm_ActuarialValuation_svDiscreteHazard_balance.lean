-- Prove2me | Theorems.Thm_ActuarialValuation_svDiscreteHazard_balance
-- name    : ActuarialValuation.svDiscreteHazard_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:39.796996+00:00
-- url     : https://prove2.me/theorems/130f69b7-8e3c-479d-b889-c30bf7a59401
-- title:
--   Measurable lifetime distributions and conditional survival: svDiscreteHazard_balance
-- statement:
--   The conditional discrete death probability multiplied by at-risk survival yields the unconditional failure mass.
--
--   Mathematical relation:
--
--   $$
--   svDiscreteHazard\_balance
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

theorem svDiscreteHazard_balance (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) (h0 : svSurvival μ T ((k:ℝ)-1) ≠ 0) (hfin : svSurvival μ T ((k:ℝ)-1) ≠ ⊤) : svDiscreteHazard μ T k * svSurvival μ T ((k:ℝ)-1) = svFailureMass μ T k := by sorry

end ActuarialValuation
