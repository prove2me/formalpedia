-- Prove2me | Theorems.Thm_ActuarialValuation_svInsurancePV_const
-- name    : ActuarialValuation.svInsurancePV_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:26:30.596688+00:00
-- url     : https://prove2.me/theorems/6c7505c2-e7a5-4f4d-a0ba-2d9fb24bee2b
-- title:
--   Exponential Gompertz Makeham hazards and insurance valuation: svInsurancePV_const
-- statement:
--   A deterministic real-valued lifetime has an insurance present-value expectation equal to the discounted fixed-time claim.
--
--   Mathematical relation:
--
--   $$
--   svInsurancePV\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svInsurancePresentValue

namespace ActuarialValuation

theorem svInsurancePV_const (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (r delta : ℝ) : svInsurancePresentValue μ (fun _ => r) delta = Real.exp (-delta*r) := by sorry

end ActuarialValuation
