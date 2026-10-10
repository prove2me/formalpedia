-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerBiasedSuccess_zero
-- name    : ActuarialValuation.gamblerBiasedSuccess_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:27.631047+00:00
-- url     : https://prove2.me/theorems/af4e1ba8-39c2-4c59-9ea3-89f340925ee1
-- title:
--   Biased capital success candidate is zero at the lower boundary
-- statement:
--   At capital zero, the numerator is one minus any real odds ratio to the power zero, which is zero. Therefore the biased success candidate vanishes even before checking the nonzero normalising denominator.
--
--   **Mathematical statement**
--
--   $$
--   H_p(0)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerBiasedSuccess_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerBiasedSuccess

namespace ActuarialValuation

theorem gamblerBiasedSuccess_zero (N : ℕ) (p : ℝ) :
  gamblerBiasedSuccess N 0 p = 0 := by sorry

end ActuarialValuation
