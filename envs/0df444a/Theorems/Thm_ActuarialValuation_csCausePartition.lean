-- Prove2me | Theorems.Thm_ActuarialValuation_csCausePartition
-- name    : ActuarialValuation.csCausePartition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:29.051391+00:00
-- url     : https://prove2.me/theorems/2a12743f-d665-4ff1-8af2-3e14480551a9
-- title:
--   Actual joint-lifetime events and cause partition: csCausePartition
-- statement:
--   Three disjoint strict first-cause events exhaust probability when pairwise primitive ties have zero mass.
--
--   Mathematical relation:
--
--   $$
--   csCausePartition
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseOne
import Definitions.Def_actuarial_csCauseTwo
import Definitions.Def_actuarial_csShockCause
import Definitions.Def_actuarial_csPrimitiveTie

namespace ActuarialValuation

theorem csCausePartition {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hU : Measurable U) (hV : Measurable V) (hZ : Measurable Z) (htie : csPrimitiveTie μ U V Z = 0) : csCauseOne μ U V Z + csCauseTwo μ U V Z + csShockCause μ U V Z = 1 := by sorry

end ActuarialValuation
