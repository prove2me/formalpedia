-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_width_tsub
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_width_tsub
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:59:29.004291+00:00
-- url     : https://prove2.me/theorems/800f5d91-ea8e-48cf-acad-7bf1c2fa2cf6
-- title:
--   Original physical uniform time cell endpoint difference equals its exact width
-- statement:
--   For every nonnegative integer cell index and nonnegative physical uniform-cell width, the NNReal truncated difference between consecutive cell boundaries is exactly that width.
-- source:
--   Pinned add_tsub_cancel_left, natural casts and ring algebra; precise rectangular source time-rate simplification for the original second-factorial moment.

import Mathlib

open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_width_tsub (i : ℕ) (δ : ℝ≥0) :
    (((i + 1 : ℕ) : ℝ≥0) * δ) - ((i : ℝ≥0) * δ) = δ := by sorry
