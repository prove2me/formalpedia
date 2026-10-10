-- Prove2me | Theorems.Thm_ActuarialValuation_svShifted_survival
-- name    : ActuarialValuation.svShifted_survival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:12.750564+00:00
-- url     : https://prove2.me/theorems/3606958f-f949-4246-8098-6ffe83dee1ed
-- title:
--   Measurable lifetime distributions and conditional survival: svShifted_survival
-- statement:
--   The unconditional distribution of the shifted lifetime T minus s has exactly the corresponding shifted strict survival threshold.
--
--   Mathematical relation:
--
--   $$
--   svShifted\_survival
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
import Definitions.Def_actuarial_svShiftLifetime

namespace ActuarialValuation

theorem svShifted_survival (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) : svSurvival μ (svShiftLifetime T s) t = svSurvival μ T (s+t) := by sorry

end ActuarialValuation
