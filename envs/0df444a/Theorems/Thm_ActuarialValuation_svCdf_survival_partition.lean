-- Prove2me | Theorems.Thm_ActuarialValuation_svCdf_survival_partition
-- name    : ActuarialValuation.svCdf_survival_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:39.624826+00:00
-- url     : https://prove2.me/theorems/6d424c36-840b-4f53-8350-4b946c4da5e5
-- title:
--   Measurable lifetime distributions and conditional survival: svCdf_survival_partition
-- statement:
--   For a measurable lifetime under a probability measure, the events T at most t and T greater than t form a full disjoint partition.
--
--   Mathematical relation:
--
--   $$
--   svCdf\_survival\_partition
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

namespace ActuarialValuation

theorem svCdf_survival_partition (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT : Measurable T) (t : ℝ) : svCdf μ T t + svSurvival μ T t = 1 := by sorry

end ActuarialValuation
