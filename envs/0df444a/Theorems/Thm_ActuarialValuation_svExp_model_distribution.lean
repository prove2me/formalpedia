-- Prove2me | Theorems.Thm_ActuarialValuation_svExp_model_distribution
-- name    : ActuarialValuation.svExp_model_distribution
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:40.95978+00:00
-- url     : https://prove2.me/theorems/9cce4e54-5815-4dab-bfa9-fcdabc14958a
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svExp_model_distribution
-- statement:
--   If the actual lifetime random variable has exponential survivor law, its CDF is its complement as an identity of event probabilities.
--
--   Mathematical relation:
--
--   $$
--   svExp\_model\_distribution
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svCdf
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svExpSurvival

namespace ActuarialValuation

theorem svExp_model_distribution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT : Measurable T) (lambda t : ℝ) (hmodel : svSurvival μ T t = ENNReal.ofReal (svExpSurvival lambda t)) : svCdf μ T t + ENNReal.ofReal (svExpSurvival lambda t) = 1 := by sorry

end ActuarialValuation
