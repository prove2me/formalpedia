-- Prove2me | Theorems.Thm_ActuarialValuation_svFiniteMean_two_points
-- name    : ActuarialValuation.svFiniteMean_two_points
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:33.983226+00:00
-- url     : https://prove2.me/theorems/e49d5324-f7aa-442a-acc0-56f28c69b931
-- title:
--   Discrete failure masses and finite life expectancy: svFiniteMean_two_points
-- statement:
--   For support restricted to the zero and one durations, the first moment equals probability mass at one.
--
--   Mathematical relation:
--
--   $$
--   svFiniteMean\_two\_points
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

theorem svFiniteMean_two_points (p : ℕ → ℝ) : svFiniteMassMean p 1 = p 1 := by sorry

end ActuarialValuation
