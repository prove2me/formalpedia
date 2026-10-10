-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerBiasedSuccess_harmonic
-- name    : ActuarialValuation.gamblerBiasedSuccess_harmonic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:57.090975+00:00
-- url     : https://prove2.me/theorems/e43cb76a-0b94-4025-9f41-51d1fc03dcb6
-- title:
--   Biased capital success candidate satisfies the transition recursion
-- statement:
--   For an interior unit-stake game, the general-biased harmonic candidate uses the down-to-up odds ratio r=(1−p)/p. Its numerator solves the characteristic difference equation under nonzero p, and normalising by one minus r^N gives the exact first-step recursion whenever the denominator is nonzero.
--
--   **Mathematical statement**
--
--   $$
--   H_p(i)=pH_p(i+1)+(1-p)H_p(i-1)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerBiasedSuccess_harmonic is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerBiasedSuccess
import Definitions.Def_actuarial_gamblerOddsRatio

namespace ActuarialValuation

theorem gamblerBiasedSuccess_harmonic
  (N i : ℕ) (p : ℝ)
  (hlo : 0 < i) (hhi : i < N) (hp : p ≠ 0)
  (hden : 1 - gamblerOddsRatio p ^ N ≠ 0) :
  gamblerBiasedSuccess N i p =
    p * gamblerBiasedSuccess N (i + 1) p +
      (1 - p) * gamblerBiasedSuccess N (i - 1) p := by sorry

end ActuarialValuation
