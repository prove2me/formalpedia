-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteSuccess_nonneg
-- name    : ActuarialValuation.gamblerFiniteSuccess_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:33:41.034254+00:00
-- url     : https://prove2.me/theorems/752831cf-3282-488e-a2d7-10f9f5add6d8
-- title:
--   Valid step probabilities give nonnegative finite success chances
-- statement:
--   At zero horizon or absorbed states the success chance is zero or one. At an interior state the recursion is a convex combination of earlier nonnegative success chances, since both p and one minus p are nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   0\le p\le1\Rightarrow S_n(i)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteSuccess_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteSuccess

namespace ActuarialValuation

theorem gamblerFiniteSuccess_nonneg
  (N n i : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  0 ≤ gamblerFiniteSuccess N p n i := by sorry

end ActuarialValuation
