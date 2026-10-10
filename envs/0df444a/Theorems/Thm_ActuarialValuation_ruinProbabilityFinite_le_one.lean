-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_le_one
-- name    : ActuarialValuation.ruinProbabilityFinite_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:45.444139+00:00
-- url     : https://prove2.me/theorems/7e0e1411-a28f-48f2-aad8-532cc729e27a
-- title:
--   Normalised annual claim probabilities bound finite ruin probability by one
-- statement:
--   With an annual claim mass function summing to one, every solvent state averages predecessor-horizon ruin probabilities with nonnegative weights of total one. Since the base and already-ruined values lie at most one, induction establishes that the finite-horizon ruin probability never exceeds one.
--
--   **Mathematical statement**
--
--   $$
--   w\ge0,\ \sum_kw_k=1\Rightarrow\psi_n(u)\le1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_le_one is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinClaimMass

namespace ActuarialValuation

theorem ruinProbabilityFinite_le_one
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ)
  (hw : ∀ k, 0 ≤ w k) (hm : ruinClaimMass w B = 1) :
  ruinProbabilityFinite w B c n u ≤ 1 := by sorry

end ActuarialValuation
