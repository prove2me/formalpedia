-- Prove2me | Theorems.Thm_ActuarialValuation_ruinFiniteHorizon_fundamental
-- name    : ActuarialValuation.ruinFiniteHorizon_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:23.597615+00:00
-- url     : https://prove2.me/theorems/9847b434-419b-497c-a524-fce859391089
-- title:
--   Normalised finite ruin recursion and the Lundberg bound
-- statement:
--   The capstone formalises a bounded annual integer-claim surplus recursion with an absorbing strict-negative ruin condition. Proper nonnegative annual claim probabilities keep finite-horizon ruin probability within the unit interval. A nonnegative exponential adjustment parameter satisfying E[exp(R(X−c))]≤1 then bounds it by exp(−Ru) for every finite horizon and signed starting capital.
--
--   **Mathematical statement**
--
--   $$
--   0\le\psi_n(u)\le1,\quad M(R)\le1\Rightarrow\psi_n(u)\le e^{-Ru}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinFiniteHorizon_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinClaimMass
import Definitions.Def_actuarial_ruinAdjustmentMoment
import Definitions.Def_actuarial_ruinExponentialBound

namespace ActuarialValuation

theorem ruinFiniteHorizon_fundamental
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k)
  (hmass : ruinClaimMass w B = 1)
  (hR : 0 ≤ R)
  (hmoment : ruinAdjustmentMoment w B c R ≤ 1) :
  (0 ≤ ruinProbabilityFinite w B c n u ∧
    ruinProbabilityFinite w B c n u ≤ 1) ∧
  (ruinProbabilityFinite w B c n u ≤
    ruinExponentialBound R u) := by sorry

end ActuarialValuation
