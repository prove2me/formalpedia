-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFairSuccess_zero
-- name    : ActuarialValuation.gamblerFairSuccess_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:22.33599+00:00
-- url     : https://prove2.me/theorems/c9d7da0f-3b93-4827-98b9-ef61bf18bf77
-- title:
--   Fair harmonic function vanishes at zero capital
-- statement:
--   The fair candidate's numerator is zero at the lower absorbing boundary, so the proposed upper-barrier success probability is zero even if the target denominator is algebraically zero.
--
--   **Mathematical statement**
--
--   $$
--   H_{\rm fair}(0)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFairSuccess_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFairSuccess

namespace ActuarialValuation

theorem gamblerFairSuccess_zero (N : ℕ) :
  gamblerFairSuccess N 0 = 0 := by sorry

end ActuarialValuation
