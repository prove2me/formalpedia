-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_nonneg
-- name    : ActuarialValuation.ruinProbabilityFinite_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:24.253269+00:00
-- url     : https://prove2.me/theorems/bc0caa30-db2a-45e1-88b7-55dbc08428ef
-- title:
--   Nonnegative annual probabilities give a nonnegative finite-horizon ruin quantity
-- statement:
--   The ruin probability recursion starts from indicator values zero or one, treats already-ruined states as one, and at solvent states takes nonnegative weighted sums of earlier nonnegative values. Induction on horizon proves nonnegativity for every signed surplus.
--
--   **Mathematical statement**
--
--   $$
--   w_k\ge0\Rightarrow\psi_n(u)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

namespace ActuarialValuation

theorem ruinProbabilityFinite_nonneg
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ)
  (hw : ∀ k, 0 ≤ w k) :
  0 ≤ ruinProbabilityFinite w B c n u := by sorry

end ActuarialValuation
