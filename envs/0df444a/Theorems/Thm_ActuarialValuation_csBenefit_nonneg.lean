-- Prove2me | Theorems.Thm_ActuarialValuation_csBenefit_nonneg
-- name    : ActuarialValuation.csBenefit_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:24.868974+00:00
-- url     : https://prove2.me/theorems/9e52380e-af66-40db-b9a6-2497fc38a63b
-- title:
--   Cause-contingent actuarial benefits and dependence: csBenefit_nonneg
-- statement:
--   Nonnegative claims and nonnegative discount factor give nonnegative actual expectation over disjoint first-cause events.
--
--   Mathematical relation:
--
--   $$
--   csBenefit\_nonneg
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

theorem csBenefit_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (disc b1 b2 bz : ℝ) (hd : 0 ≤ disc) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (hz : 0 ≤ bz) : 0 ≤ csCauseInsurancePV μ U V Z disc b1 b2 bz := by sorry

end ActuarialValuation
