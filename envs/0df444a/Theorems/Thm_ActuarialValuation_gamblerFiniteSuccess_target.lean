-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteSuccess_target
-- name    : ActuarialValuation.gamblerFiniteSuccess_target
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:29.014071+00:00
-- url     : https://prove2.me/theorems/eb527932-1fe3-4263-840b-d656226fdf33
-- title:
--   Starting at positive upper target is immediate success
-- statement:
--   For positive target N, a process already at the upper absorbing barrier has succeeded before further bets. Therefore success by every finite horizon, including zero steps, has probability one.
--
--   **Mathematical statement**
--
--   $$
--   N>0\Rightarrow S_n(N)=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteSuccess_target is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteSuccess

namespace ActuarialValuation

theorem gamblerFiniteSuccess_target
  (N n : ℕ) (p : ℝ) (hN : 0 < N) :
  gamblerFiniteSuccess N p n N = 1 := by sorry

end ActuarialValuation
