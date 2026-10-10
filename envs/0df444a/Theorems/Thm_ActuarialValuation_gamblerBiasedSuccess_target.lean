-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerBiasedSuccess_target
-- name    : ActuarialValuation.gamblerBiasedSuccess_target
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:45.379858+00:00
-- url     : https://prove2.me/theorems/82c385e9-2791-4b45-9cec-d6448a9a9747
-- title:
--   Biased capital success candidate equals one at nonzero denominator
-- statement:
--   When starting at the upper barrier, the biased success formula has equal numerator and denominator. If this denominator is nonzero, the ratio equals one and satisfies the absorbing upper-boundary condition.
--
--   **Mathematical statement**
--
--   $$
--   1-r^N\ne0\Rightarrow H_p(N)=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerBiasedSuccess_target is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerOddsRatio

namespace ActuarialValuation

theorem gamblerBiasedSuccess_target
  (N : ℕ) (p : ℝ)
  (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
  gamblerBiasedSuccess N N p = 1 := by sorry

end ActuarialValuation
