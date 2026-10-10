-- Prove2me | Theorems.Thm_ActuarialValuation_svTail_succ
-- name    : ActuarialValuation.svTail_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:05.165255+00:00
-- url     : https://prove2.me/theorems/1ba1d785-c223-4cb4-815d-8effaa3d0156
-- title:
--   Discrete failure masses and finite life expectancy: svTail_succ
-- statement:
--   The finite strict tail beyond k decomposes into the next integer failure mass and the later tail.
--
--   Mathematical relation:
--
--   $$
--   svTail\_succ
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

theorem svTail_succ (p : ℕ → ℝ) (n k : ℕ) (hk : k < n) : svFiniteTailMass p n k = p (k+1) + svFiniteTailMass p n (k+1) := by sorry

end ActuarialValuation
