-- Prove2me | Theorems.Thm_ActuarialValuation_ruinExponentialBound_negative_ge_one
-- name    : ActuarialValuation.ruinExponentialBound_negative_ge_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:36.449249+00:00
-- url     : https://prove2.me/theorems/a61c84f0-21f4-4a8c-8636-6f5c381f47e8
-- title:
--   Benchmark exceeds one for negative surplus and nonnegative adjustment
-- statement:
--   For negative current surplus, minus R times surplus is nonnegative when R≥0. Its real exponential is at least one, which dominates the absorbing ruin value one. This is the essential boundary in the exponential comparison proof.
--
--   **Mathematical statement**
--
--   $$
--   R\ge0,\ u<0\Rightarrow e^{-Ru}\ge1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinExponentialBound_negative_ge_one is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinExponentialBound

namespace ActuarialValuation

theorem ruinExponentialBound_negative_ge_one
  (R : ℝ) (u : ℤ) (hR : 0 ≤ R) (hu : u < 0) :
  1 ≤ ruinExponentialBound R u := by sorry

end ActuarialValuation
