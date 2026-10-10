-- Prove2me | Theorems.Thm_ActuarialValuation_svSurvival_start
-- name    : ActuarialValuation.svSurvival_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:57.434494+00:00
-- url     : https://prove2.me/theorems/2939a172-b125-4e38-940c-3189c40a6dab
-- title:
--   Measurable lifetime distributions and conditional survival: svSurvival_start
-- statement:
--   Unit survival at issue requires lifetime strictly positive almost surely; a mass at zero would violate it.
--
--   Mathematical relation:
--
--   $$
--   svSurvival\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvival

namespace ActuarialValuation

theorem svSurvival_start (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT0 : ∀ ω, 0 < T ω) : svSurvival μ T 0 = 1 := by sorry

end ActuarialValuation
