-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_zero
-- name    : ActuarialValuation.ruinProbabilityFinite_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:28:54.81193+00:00
-- url     : https://prove2.me/theorems/0876129c-058c-4c44-a42b-57904e5e5555
-- title:
--   The zero-year ruin indicator detects negative initial surplus
-- statement:
--   Before any annual claim periods pass, ruin has occurred exactly when the insurer's starting surplus is already strictly below zero. This convention distinguishes strict ruin from hitting zero capital.
--
--   **Mathematical statement**
--
--   $$
--   \psi_0(u)=\mathbf1_{\{u<0\}}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_zero is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

namespace ActuarialValuation

theorem ruinProbabilityFinite_zero
  (w : ℕ → ℝ) (B c : ℕ) (u : ℤ) :
  ruinProbabilityFinite w B c 0 u = (if u < 0 then 1 else 0) := by sorry

end ActuarialValuation
