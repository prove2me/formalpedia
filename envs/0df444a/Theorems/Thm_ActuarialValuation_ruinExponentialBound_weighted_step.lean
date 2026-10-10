-- Prove2me | Theorems.Thm_ActuarialValuation_ruinExponentialBound_weighted_step
-- name    : ActuarialValuation.ruinExponentialBound_weighted_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:11.262788+00:00
-- url     : https://prove2.me/theorems/e1303e52-610c-4d8a-b79e-52fbf3940f73
-- title:
--   Expected next-state exponential benchmark factors by the adjustment moment
-- statement:
--   Using the pathwise exponential factorisation, the weighted expectation of the next-state exponential benchmark is the current exponential benchmark times the net-loss exponential moment. This identity is the exact finite-state form underlying Lundberg's exponential risk bound.
--
--   **Mathematical statement**
--
--   $$
--   \sum_kw_ke^{-R(u+c-k)}=e^{-Ru}M(R)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinExponentialBound_weighted_step is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus
import Definitions.Def_actuarial_ruinAdjustmentMoment

namespace ActuarialValuation

theorem ruinExponentialBound_weighted_step
  (w : ℕ → ℝ) (B c : ℕ) (R : ℝ) (u : ℤ) :
  (∑ k ∈ Finset.range (B + 1),
     w k * ruinExponentialBound R (ruinNextSurplus u c k)) =
    ruinExponentialBound R u *
      ruinAdjustmentMoment w B c R := by sorry

end ActuarialValuation
