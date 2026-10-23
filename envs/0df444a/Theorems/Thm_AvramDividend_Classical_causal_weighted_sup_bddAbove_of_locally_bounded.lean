-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
-- name    : AvramDividend.Classical.causal_weighted_sup_bddAbove_of_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:52:56.170767+00:00
-- url     : https://prove2.me/theorems/f9209e29-ed60-423f-b46e-ceaaa698043c
-- title:
--   Local boundedness implies a bounded exponentially weighted finite-horizon supremum
-- statement:
--   For a locally bounded real function on positive half-line intervals and nonnegative exponential weight, its damped absolute value has a bounded range on each finite interval. Since t is positive and weight nonnegative, exp(-wt)≤1, so each damped value is at most the original local bound. This is a deterministic prerequisite for weighted Volterra uniqueness.
-- source:
--   Direct exponential monotonicity and BddAbove of an image; part of causal Volterra uniqueness under local boundedness.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.ConditionallyCompleteLattice.Basic
open Set

theorem AvramDividend.Classical.causal_weighted_sup_bddAbove_of_locally_bounded
    (D : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ t : ℝ, t ∈ Ioc (0 : ℝ) R → |D t| ≤ C) :
    ∀ R : ℝ, 0 < R →
      BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
        Ioc (0 : ℝ) R) := by sorry
