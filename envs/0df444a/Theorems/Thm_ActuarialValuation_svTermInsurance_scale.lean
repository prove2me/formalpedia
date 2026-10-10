-- Prove2me | Theorems.Thm_ActuarialValuation_svTermInsurance_scale
-- name    : ActuarialValuation.svTermInsurance_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:19.407306+00:00
-- url     : https://prove2.me/theorems/8d1143c8-5f71-4339-adcc-2cd318bee572
-- title:
--   Discrete failure masses and finite life expectancy: svTermInsurance_scale
-- statement:
--   Term-insurance expected present value scales linearly in the realised death-year mass measure.
--
--   Mathematical relation:
--
--   $$
--   svTermInsurance\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTermInsurance

namespace ActuarialValuation

theorem svTermInsurance_scale (p d : ℕ → ℝ) (n : ℕ) (a : ℝ) : svFiniteTermInsurance (fun k => a*p k) d n = a * svFiniteTermInsurance p d n := by sorry

end ActuarialValuation
