-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteRuin_zero_capital
-- name    : ActuarialValuation.gamblerFiniteRuin_zero_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:47.377986+00:00
-- url     : https://prove2.me/theorems/339edff1-ff3b-40a9-a97a-9f477a286986
-- title:
--   Starting at zero capital means ruin has already happened
-- statement:
--   Starting exactly at the lower absorbing state is ruin under the gambler's ruin convention. The finite-horizon ruin indicator is therefore one, unlike the separate insurance reserve mission where ruin required strictly negative surplus.
--
--   **Mathematical statement**
--
--   $$
--   R_n(0)=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteRuin_zero_capital is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteRuin

namespace ActuarialValuation

theorem gamblerFiniteRuin_zero_capital (N n : ℕ) (p : ℝ) :
  gamblerFiniteRuin N p n 0 = 1 := by sorry

end ActuarialValuation
