-- Prove2me | Theorems.Thm_ActuarialValuation_csCauseInsurancePV_zero
-- name    : ActuarialValuation.csCauseInsurancePV_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:05.570118+00:00
-- url     : https://prove2.me/theorems/17a447af-3b61-4479-9f2e-44f92b294b21
-- title:
--   Cause-contingent actuarial benefits and dependence: csCauseInsurancePV_zero
-- statement:
--   Zero cause-contingent benefit amounts produce zero actuarial present value.
--
--   Mathematical relation:
--
--   $$
--   csCauseInsurancePV\_zero
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

namespace ActuarialValuation

theorem csCauseInsurancePV_zero {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (disc : ℝ) : csCauseInsurancePV μ U V Z disc 0 0 0 = 0 := by sorry

end ActuarialValuation
