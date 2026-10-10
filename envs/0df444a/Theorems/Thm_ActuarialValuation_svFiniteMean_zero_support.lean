-- Prove2me | Theorems.Thm_ActuarialValuation_svFiniteMean_zero_support
-- name    : ActuarialValuation.svFiniteMean_zero_support
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:17.021435+00:00
-- url     : https://prove2.me/theorems/f30f5e85-066f-4ef1-bf89-b378f287f623
-- title:
--   Discrete failure masses and finite life expectancy: svFiniteMean_zero_support
-- statement:
--   A failure-time distribution entirely supported at duration zero has zero first moment.
--
--   Mathematical relation:
--
--   $$
--   svFiniteMean\_zero\_support
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteMassMean

namespace ActuarialValuation

theorem svFiniteMean_zero_support (p : ℕ → ℝ) : svFiniteMassMean p 0 = 0 := by sorry

end ActuarialValuation
