-- Prove2me | Theorems.Thm_ActuarialValuation_ruinAdjustmentMoment_nonneg
-- name    : ActuarialValuation.ruinAdjustmentMoment_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:29:59.292054+00:00
-- url     : https://prove2.me/theorems/1c8211eb-a871-4e4f-9578-7e8d3a3a1363
-- title:
--   Positive exponential factors preserve nonnegative weighted adjustment moment
-- statement:
--   For each bounded claim the exponential adjustment factor is strictly positive for any real R. Multiplying by a nonnegative claim probability and summing yields a nonnegative exponential moment.
--
--   **Mathematical statement**
--
--   $$
--   w\ge0\Rightarrow M(R)\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 23, Section 23.3, printed page 432 (Library PDF page 458), parent framework: Theorem 23.4 (Lundberg ruin bound). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://stats.libretexts.org/Bookshelves/Probability_Theory/Introductory_Probability_%28Grinstead_and_Snell%29/12%3A_Random_Walks/12.02%3A_Gambler%27s_Ruin. The specific Lean declaration ActuarialValuation.ruinAdjustmentMoment_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinAdjustmentMoment

namespace ActuarialValuation

theorem ruinAdjustmentMoment_nonneg
  (w : ℕ → ℝ) (B c : ℕ) (R : ℝ)
  (hw : ∀ k, 0 ≤ w k) :
  0 ≤ ruinAdjustmentMoment w B c R := by sorry

end ActuarialValuation
