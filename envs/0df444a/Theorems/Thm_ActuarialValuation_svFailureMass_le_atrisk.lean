-- Prove2me | Theorems.Thm_ActuarialValuation_svFailureMass_le_atrisk
-- name    : ActuarialValuation.svFailureMass_le_atrisk
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:15.508312+00:00
-- url     : https://prove2.me/theorems/ed57bb98-b041-44ed-9bd1-6913140b2e4c
-- title:
--   Measurable lifetime distributions and conditional survival: svFailureMass_le_atrisk
-- statement:
--   Any failure occurring at a positive integer k lies within the population surviving beyond k minus one.
--
--   Mathematical relation:
--
--   $$
--   svFailureMass\_le\_atrisk
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFailureMass
import Definitions.Def_actuarial_svSurvival

namespace ActuarialValuation

theorem svFailureMass_le_atrisk (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) (hk : 0 < k) : svFailureMass μ T k ≤ svSurvival μ T ((k:ℝ)-1) := by sorry

end ActuarialValuation
