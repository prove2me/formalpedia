-- Prove2me | Theorems.Thm_ActuarialValuation_csCauseInsurancePV_scale
-- name    : ActuarialValuation.csCauseInsurancePV_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:35:32.527827+00:00
-- url     : https://prove2.me/theorems/e02effdf-1b69-491f-b36c-befd5a7f1a58
-- title:
--   Cause-contingent actuarial benefits and dependence: csCauseInsurancePV_scale
-- statement:
--   The actuarial valuation of a fixed-time three-cause contract is homogeneous in all cause benefits.
--
--   Mathematical relation:
--
--   $$
--   csCauseInsurancePV\_scale
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

theorem csCauseInsurancePV_scale {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (disc b1 b2 bz k : ℝ) : csCauseInsurancePV μ U V Z disc (k*b1) (k*b2) (k*bz) = k * csCauseInsurancePV μ U V Z disc b1 b2 bz := by sorry

end ActuarialValuation
