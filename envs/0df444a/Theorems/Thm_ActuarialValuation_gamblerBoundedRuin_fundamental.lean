-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerBoundedRuin_fundamental
-- name    : ActuarialValuation.gamblerBoundedRuin_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:34:44.105695+00:00
-- url     : https://prove2.me/theorems/f86e9458-4b35-4a37-9712-faa42c44dfe2
-- title:
--   Fair and biased harmonic capital functions alongside finite absorption bounds
-- statement:
--   The capstone formalises the correct first-step harmonic equations for the fair and biased finite-capital random walk and nonnegative bounded finite-horizon absorption-event probabilities. Unlike an infinite-horizon gambler's ruin theorem, it does not assert that every path has already been absorbed by a finite horizon or identify finite success directly with the harmonic candidate.
--
--   **Mathematical statement**
--
--   $$
--   H_{1/2}(i)=\tfrac12(H_{1/2}(i+1)+H_{1/2}(i-1)),\quad H_p(i)=pH_p(i+1)+(1-p)H_p(i-1)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerBoundedRuin_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFairSuccess
import Definitions.Def_actuarial_gamblerOddsRatio
import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerFiniteSuccess
import Definitions.Def_actuarial_gamblerFiniteRuin

namespace ActuarialValuation

theorem gamblerBoundedRuin_fundamental
  (N i n : ℕ) (p : ℝ)
  (hlo : 0 < i) (hhi : i < N)
  (hp0 : 0 < p) (hp1 : p ≤ 1)
  (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
  (gamblerFairSuccess N i =
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i + 1)) +
    ((1 / 2 : ℝ) * gamblerFairSuccess N (i - 1))) ∧
  (gamblerBiasedSuccess N i p =
    p * gamblerBiasedSuccess N (i + 1) p +
      (1 - p) * gamblerBiasedSuccess N (i - 1) p) ∧
  (0 ≤ gamblerFiniteSuccess N p n i ∧
    0 ≤ gamblerFiniteRuin N p n i ∧
    gamblerFiniteSuccess N p n i + gamblerFiniteRuin N p n i ≤ 1) := by sorry

end ActuarialValuation
