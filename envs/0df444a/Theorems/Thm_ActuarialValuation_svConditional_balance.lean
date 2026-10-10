-- Prove2me | Theorems.Thm_ActuarialValuation_svConditional_balance
-- name    : ActuarialValuation.svConditional_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:38.151982+00:00
-- url     : https://prove2.me/theorems/5cf2fca2-1f4b-4bdc-8a66-52ffc49b746e
-- title:
--   Measurable lifetime distributions and conditional survival: svConditional_balance
-- statement:
--   Conditional survivor ratio reconstructs the later survivor mass provided the at-risk probability is nonzero and finite.
--
--   Mathematical relation:
--
--   $$
--   svConditional\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svConditionalSurvival
import Definitions.Def_actuarial_svSurvival

namespace ActuarialValuation

theorem svConditional_balance (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) (h0 : svSurvival μ T s ≠ 0) (hfin : svSurvival μ T s ≠ ⊤) : svConditionalSurvival μ T s t * svSurvival μ T s = svSurvival μ T (s+t) := by sorry

end ActuarialValuation
