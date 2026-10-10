-- Prove2me | Theorems.Thm_ActuarialValuation_ruinClaimMass_nonneg
-- name    : ActuarialValuation.ruinClaimMass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:28:31.651621+00:00
-- url     : https://prove2.me/theorems/a096b0ce-8753-42f3-94a5-aa27eb0c584f
-- title:
--   Nonnegative annual claim coefficients have nonnegative total mass
-- statement:
--   Each possible annual loss has nonnegative probability mass. Their finite sum over all bounded claim amounts is consequently nonnegative, independently of whether the array has been correctly normalised.
--
--   **Mathematical statement**
--
--   $$
--   w_k\ge0\Rightarrow \sum_{k=0}^{B}w_k\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinClaimMass_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinClaimMass

namespace ActuarialValuation

theorem ruinClaimMass_nonneg (w : ℕ → ℝ) (B : ℕ)
  (hw : ∀ k, 0 ≤ w k) : 0 ≤ ruinClaimMass w B := by sorry

end ActuarialValuation
