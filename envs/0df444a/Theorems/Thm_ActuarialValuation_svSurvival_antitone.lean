-- Prove2me | Theorems.Thm_ActuarialValuation_svSurvival_antitone
-- name    : ActuarialValuation.svSurvival_antitone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:59.514602+00:00
-- url     : https://prove2.me/theorems/0ee2c7ea-22c7-4514-a233-faf93759cc12
-- title:
--   Measurable lifetime distributions and conditional survival: svSurvival_antitone
-- statement:
--   Survival probabilities decrease as the required attained survival time increases.
--
--   Mathematical relation:
--
--   $$
--   svSurvival\_antitone
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

namespace ActuarialValuation

theorem svSurvival_antitone (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) (hst : s ≤ t) : svSurvival μ T t ≤ svSurvival μ T s := by sorry

end ActuarialValuation
