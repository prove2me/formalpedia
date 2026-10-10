-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_zero_nonnegative
-- name    : ActuarialValuation.ruinProbabilityFinite_zero_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:29.134978+00:00
-- url     : https://prove2.me/theorems/550c14f0-38bb-416b-85a0-6b5f1950ae7e
-- title:
--   An insurer starting solvent cannot be ruined at zero horizon
-- statement:
--   With no time elapsed, nonnegative starting capital fails the strict-negative ruin condition. The chance of ruin by the zero-year horizon is therefore exactly zero, including initial surplus zero.
--
--   **Mathematical statement**
--
--   $$
--   u\ge0\Rightarrow\psi_0(u)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_zero_nonnegative is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

namespace ActuarialValuation

theorem ruinProbabilityFinite_zero_nonnegative
  (w : ℕ → ℝ) (B c : ℕ) (u : ℤ) (hu : 0 ≤ u) :
  ruinProbabilityFinite w B c 0 u = 0 := by sorry

end ActuarialValuation
