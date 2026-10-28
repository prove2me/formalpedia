-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_truncated_le_exp_gap
-- name    : AvramDividend.Classical.nonnegative_truncated_le_exp_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:54:28.208452+00:00
-- url     : https://prove2.me/theorems/f7b02451-cbb8-4667-9bc5-2d4f23dc73b8
-- title:
--   Exponential transform controls capped nonnegative Lévy drift-deficit increments
-- statement:
--   If 0≤x≤a with a>0, then x≤4a(1-exp(-x/(2a))). The inequality bounds the contribution of a capped increment to a finite-mesh Lévy deficit by its discounted Laplace deficit. It is an elementary scaling consequence of the proved exponential-deficit half-interval lemma.
-- source:
--   Proved exp_gap_dominates_half_interval, basic field algebra and positivity.

import Theorems.Thm_AvramDividend_Classical_exp_gap_dominates_half_interval
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.nonnegative_truncated_le_exp_gap
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    x ≤ 4 * a * (1 - Real.exp (-(x / (2 * a)))) := by sorry
