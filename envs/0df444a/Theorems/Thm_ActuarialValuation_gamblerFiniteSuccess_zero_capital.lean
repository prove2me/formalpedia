-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteSuccess_zero_capital
-- name    : ActuarialValuation.gamblerFiniteSuccess_zero_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:11.295695+00:00
-- url     : https://prove2.me/theorems/458bce17-3453-42df-a762-478d24ff3bc1
-- title:
--   Starting ruined prevents finite-horizon upper-barrier success
-- statement:
--   The unit-stake process treats zero capital as an absorbing losing state, so it cannot later reach the upper target even with arbitrary remaining horizon. The source's capital-zero branch evaluates to zero.
--
--   **Mathematical statement**
--
--   $$
--   S_n(0)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteSuccess_zero_capital is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteSuccess

namespace ActuarialValuation

theorem gamblerFiniteSuccess_zero_capital (N n : ℕ) (p : ℝ) :
  gamblerFiniteSuccess N p n 0 = 0 := by sorry

end ActuarialValuation
