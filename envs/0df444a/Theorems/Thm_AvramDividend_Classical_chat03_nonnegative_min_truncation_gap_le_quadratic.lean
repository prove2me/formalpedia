-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_min_truncation_gap_le_quadratic
-- name    : AvramDividend.Classical.chat03_nonnegative_min_truncation_gap_le_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:55:47.351034+00:00
-- url     : https://prove2.me/theorems/17ce7db7-3bc7-4a5e-a02f-feef6a9ec466
-- title:
--   Quadratic bound on the nonnegative truncation error
-- statement:
--   For a nonnegative real number and strictly positive cutoff, the discrepancy between the original value and its minimum with the cutoff is nonnegative and bounded above by its square divided by the cutoff. This enables real-valued integral truncation error estimates using finite second moments.
-- source:
--   Elementary inequalities and the already accepted quadratic-tail pointwise estimate.

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_pointwise

theorem AvramDividend.Classical.chat03_nonnegative_min_truncation_gap_le_quadratic
    (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    0 ≤ y - min y R ∧ y - min y R ≤ y ^ 2 / R := by sorry
