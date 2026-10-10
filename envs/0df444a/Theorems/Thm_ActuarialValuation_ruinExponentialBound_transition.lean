-- Prove2me | Theorems.Thm_ActuarialValuation_ruinExponentialBound_transition
-- name    : ActuarialValuation.ruinExponentialBound_transition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:52.267984+00:00
-- url     : https://prove2.me/theorems/35f7e90e-4847-4fb7-9b01-79a50b2c9fc4
-- title:
--   Exponential benchmark factors across a surplus update
-- statement:
--   The insurer's next surplus equals current signed surplus plus premium minus claim. Exponentiating minus R times this result factors into current benchmark exp(−Ru) and the exponential of the net annual claim loss R(k−c), enabling a one-step martingale comparison.
--
--   **Mathematical statement**
--
--   $$
--   e^{-R(u+c-k)}=e^{-Ru}e^{R(k-c)}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinExponentialBound_transition is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound
import Definitions.Def_actuarial_ruinNextSurplus

namespace ActuarialValuation

theorem ruinExponentialBound_transition
  (R : ℝ) (u : ℤ) (c k : ℕ) :
  ruinExponentialBound R (ruinNextSurplus u c k) =
    ruinExponentialBound R u *
      Real.exp (R * ((k : ℝ) - (c : ℝ))) := by sorry

end ActuarialValuation
