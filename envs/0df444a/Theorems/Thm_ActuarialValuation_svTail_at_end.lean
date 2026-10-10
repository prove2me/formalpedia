-- Prove2me | Theorems.Thm_ActuarialValuation_svTail_at_end
-- name    : ActuarialValuation.svTail_at_end
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:45.792861+00:00
-- url     : https://prove2.me/theorems/ae466745-e48d-4112-a5e6-49d1769b2115
-- title:
--   Discrete failure masses and finite life expectancy: svTail_at_end
-- statement:
--   No remaining probability lies strictly above the finite maximum supported failure time n.
--
--   Mathematical relation:
--
--   $$
--   svTail\_at\_end
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 14, 8 and Appendix A, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.actuaries.org.uk/system/files/field/document/Technical%20Workshop%20October%202019%20Slide%20Deck.pdf. Published source page 211 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTailMass

namespace ActuarialValuation

theorem svTail_at_end (p : ℕ → ℝ) (n : ℕ) : svFiniteTailMass p n n = 0 := by sorry

end ActuarialValuation
