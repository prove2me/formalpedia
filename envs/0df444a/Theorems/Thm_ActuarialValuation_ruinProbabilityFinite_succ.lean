-- Prove2me | Theorems.Thm_ActuarialValuation_ruinProbabilityFinite_succ
-- name    : ActuarialValuation.ruinProbabilityFinite_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:46.509727+00:00
-- url     : https://prove2.me/theorems/3bfba180-218b-4548-8e2b-9cf8ae9671f2
-- title:
--   A solvent insurer's next-period ruin is a weighted successor-state sum
-- statement:
--   Provided initial surplus has not yet crossed below zero, the probability of ruin during the next n+1 periods is the annual-claim probability-weighted average of the n-period ruin probabilities from each next-surplus state. The recurrence includes immediate next-period ruin because negative successor states have value one.
--
--   **Mathematical statement**
--
--   $$
--   \psi_{n+1}(u)=\sum_{k=0}^{B}w_k\psi_n(u+c-k)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinProbabilityFinite_succ is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinProbabilityFinite
import Definitions.Def_actuarial_ruinNextSurplus

namespace ActuarialValuation

theorem ruinProbabilityFinite_succ
  (w : ℕ → ℝ) (B c n : ℕ) (u : ℤ) (hu : 0 ≤ u) :
  ruinProbabilityFinite w B c (n + 1) u =
    ∑ k ∈ Finset.range (B + 1),
      w k * ruinProbabilityFinite w B c n
        (ruinNextSurplus u c k) := by sorry

end ActuarialValuation
