-- Prove2me | Theorems.Thm_ActuarialValuation_svSurvivalHazardInsurance_fundamental
-- name    : ActuarialValuation.svSurvivalHazardInsurance_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:26:48.768018+00:00
-- url     : https://prove2.me/theorems/61b7450e-0169-4459-8af9-b84c0875c302
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svSurvivalHazardInsurance_fundamental
-- statement:
--   The capstone combines genuine probability-measure lifetime CDF reconciliation under an explicit exponential survivor-law hypothesis, cumulative-hazard reconstruction, and the actual expected unit insurance present value at zero interest.
--
--   Mathematical relation:
--
--   $$
--   svSurvivalHazardInsurance\_fundamental
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
import Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
import Definitions.Def_actuarial_svExpCumulativeHazard
import Definitions.Def_actuarial_svInsurancePresentValue

namespace ActuarialValuation

theorem svSurvivalHazardInsurance_fundamental (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (T : Ω → ℝ) (hT : Measurable T) (t lambda : ℝ) (hmodel : svSurvival μ T t = ENNReal.ofReal (svExpSurvival lambda t)) : (svCdf μ T t + ENNReal.ofReal (svExpSurvival lambda t) = 1) ∧ (svSurvivalFromCumulativeHazard (svExpCumulativeHazard lambda t) = svExpSurvival lambda t) ∧ (svInsurancePresentValue μ T 0 = 1) := by sorry

end ActuarialValuation
