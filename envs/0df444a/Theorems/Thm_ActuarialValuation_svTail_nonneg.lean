-- Prove2me | Theorems.Thm_ActuarialValuation_svTail_nonneg
-- name    : ActuarialValuation.svTail_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:27.550043+00:00
-- url     : https://prove2.me/theorems/8ceb978b-a7d4-4b29-9837-5d229165273c
-- title:
--   Discrete failure masses and finite life expectancy: svTail_nonneg
-- statement:
--   Finite discrete survival mass is nonnegative whenever individual mass assignments are nonnegative.
--
--   Mathematical relation:
--
--   $$
--   svTail\_nonneg
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

theorem svTail_nonneg (p : ℕ → ℝ) (n k : ℕ) (hp : ∀ j ∈ Finset.Icc (k+1) n, 0 ≤ p j) : 0 ≤ svFiniteTailMass p n k := by sorry

end ActuarialValuation
