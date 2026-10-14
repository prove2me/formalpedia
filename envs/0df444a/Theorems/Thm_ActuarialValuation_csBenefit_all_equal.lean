-- Prove2me | Theorems.Thm_ActuarialValuation_csBenefit_all_equal
-- name    : ActuarialValuation.csBenefit_all_equal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:51:43.944372+00:00
-- url     : https://prove2.me/theorems/2c2ca9f6-c216-41c5-9607-5f3063b1c3e0
-- title:
--   Cause-contingent actuarial benefits and dependence: csBenefit_all_equal
-- statement:
--   If every cause pays the same cash amount and one first cause occurs surely with no primitive ties, total claim value equals the fixed discounted amount.
--
--   Mathematical relation:
--
--   $$
--   csBenefit\_all\_equal
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseInsurancePV
import Definitions.Def_actuarial_csPrimitiveTie

namespace ActuarialValuation

theorem csBenefit_all_equal {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (disc b : ℝ) (hU : Measurable U) (hV : Measurable V) (hZ : Measurable Z) (htie : csPrimitiveTie μ U V Z = 0) : csCauseInsurancePV μ U V Z disc b b b = disc * b := by sorry

end ActuarialValuation
