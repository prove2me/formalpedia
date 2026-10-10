-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFairSuccess_harmonic
-- name    : ActuarialValuation.gamblerFairSuccess_harmonic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:55.001034+00:00
-- url     : https://prove2.me/theorems/3c8923ef-e649-4064-8622-bfa58d1fe998
-- title:
--   Fair capital success function satisfies interior mean-value recursion
-- statement:
--   For an interior positive integer capital the fair-game expected next harmonic value averages the upper and lower unit-step candidates. The linear function i/N exactly equals this average, with the lower step staying inside the finite state interval.
--
--   **Mathematical statement**
--
--   $$
--   H(i)=\frac{H(i+1)+H(i-1)}2
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFairSuccess_harmonic is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFairSuccess

namespace ActuarialValuation

theorem gamblerFairSuccess_harmonic
  (N i : ℕ) (hlo : 0 < i) (hhi : i < N) :
  gamblerFairSuccess N i =
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i + 1)) +
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i - 1)) := by sorry

end ActuarialValuation
