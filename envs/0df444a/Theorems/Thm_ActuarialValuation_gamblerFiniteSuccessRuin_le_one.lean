-- Prove2me | Theorems.Thm_ActuarialValuation_gamblerFiniteSuccessRuin_le_one
-- name    : ActuarialValuation.gamblerFiniteSuccessRuin_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:34:17.969986+00:00
-- url     : https://prove2.me/theorems/121c5d6e-1610-45ba-9604-e92f135787a1
-- title:
--   Finite success plus finite ruin cannot exceed one
-- statement:
--   The events of hitting the upper target or zero capital within the finite horizon are disjoint, while some paths may remain in interior states. Their probabilities therefore sum to at most one, with strict inequality possible before absorption is complete.
--
--   **Mathematical statement**
--
--   $$
--   S_n(i)+R_n(i)\le1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 427 (Library PDF page 453), parent framework: Examples 23.4–23.5 (gambler's ruin). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.gamblerFiniteSuccessRuin_le_one is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gamblerFiniteSuccess
import Definitions.Def_actuarial_gamblerFiniteRuin

namespace ActuarialValuation

theorem gamblerFiniteSuccessRuin_le_one
  (N n i : ℕ) (p : ℝ)
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hN : 0 < N) :
  gamblerFiniteSuccess N p n i + gamblerFiniteRuin N p n i ≤ 1 := by sorry

end ActuarialValuation
