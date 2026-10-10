-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_negative
-- name    : ActuarialValuation.ruinProbabilityFinite_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:11.134984+00:00
-- url     : https://prove2.me/theorems/e7e51486-a520-4c43-96d3-03cecc0d1252
-- title:
--   Once capital is negative the model is ruined at every horizon
-- statement:
--   The recursion marks an already-negative surplus as ruined with probability one, without considering future premium income or claim outcomes. This absorbing first-passage convention holds for every finite horizon.
--
--   **Mathematical statement**
--
--   $$
--   u<0\Rightarrow\psi_n(u)=1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_negative is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite

namespace ActuarialValuation

theorem ruinProbabilityFinite_negative
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (hu : u < 0) :
  ruinProbabilityFinite w B c n u = 1 := by sorry

end ActuarialValuation
