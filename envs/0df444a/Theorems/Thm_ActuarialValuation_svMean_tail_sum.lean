-- Prove2me | Theorems.Thm_ActuarialValuation_svMean_tail_sum
-- name    : ActuarialValuation.svMean_tail_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:46.223699+00:00
-- url     : https://prove2.me/theorems/aeb9c163-d222-49a7-abc4-1608a4a36248
-- title:
--   Discrete failure masses and finite life expectancy: svMean_tail_sum
-- statement:
--   For a finitely supported nonnegative-integer lifetime, expectation equals the sum of strict tail masses, including the duration-zero boundary.
--
--   Mathematical relation:
--
--   $$
--   svMean\_tail\_sum
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
import Definitions.Def_actuarial_svFiniteTailMass

namespace ActuarialValuation

theorem svMean_tail_sum (p : ℕ → ℝ) (n : ℕ) : svFiniteMassMean p n = ∑ k ∈ Finset.range n, svFiniteTailMass p n k := by sorry

end ActuarialValuation
