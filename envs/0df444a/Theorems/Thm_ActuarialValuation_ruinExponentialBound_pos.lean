-- Prove2me | Theorems.Thm_ActuarialValuation_ruinExponentialBound_pos
-- name    : ActuarialValuation.ruinExponentialBound_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:20.881981+00:00
-- url     : https://prove2.me/theorems/3881ee7e-ccb0-4567-a84c-4d7d320d0c00
-- title:
--   Lundberg benchmark is strictly positive
-- statement:
--   The exponential of any real number is strictly positive. Therefore the adjustment benchmark exp(−Ru) is positive even at negative initial surplus or negative adjustment parameters, although an actuarial upper bound will impose R≥0.
--
--   **Mathematical statement**
--
--   $$
--   L_R(u)>0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinExponentialBound_pos is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound

namespace ActuarialValuation

theorem ruinExponentialBound_pos (R : ℝ) (u : ℤ) :
  0 < ruinExponentialBound R u := by sorry

end ActuarialValuation
