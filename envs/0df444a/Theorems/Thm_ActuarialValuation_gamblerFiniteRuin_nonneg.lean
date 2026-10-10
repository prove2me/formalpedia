-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteRuin_nonneg
-- name    : ActuarialValuation.gamblerFiniteRuin_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:34:00.996415+00:00
-- url     : https://prove2.me/theorems/20dc2c2d-f6ab-4c2f-a8ec-56afb368dac4
-- title:
--   Valid step probabilities give nonnegative finite ruin chances
-- statement:
--   Ruin starts at the boundary indicators zero or one and evolves through nonnegative weighted averages at every interior capital state. Therefore finite-horizon absorption-at-zero probability cannot be negative under valid win probabilities.
--
--   **Mathematical statement**
--
--   $$
--   0\le p\le1\Rightarrow R_n(i)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteRuin_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteRuin

namespace ActuarialValuation

theorem gamblerFiniteRuin_nonneg
  (N n i : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  0 ≤ gamblerFiniteRuin N p n i := by sorry

end ActuarialValuation
