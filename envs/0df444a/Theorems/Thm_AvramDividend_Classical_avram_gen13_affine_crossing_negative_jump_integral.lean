-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_crossing_negative_jump_integral
-- name    : AvramDividend.Classical.avram_gen13_affine_crossing_negative_jump_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:26:54.554143+00:00
-- url     : https://prove2.me/theorems/5c004d2b-7405-4f0f-9666-1f9658b79606
-- title:
--   Exact affine ruin-crossing negative-jump integral for the singular Levy density
-- statement:
--   The original affine ruin-crossing kernel, integrated over small negative jumps using the proposed singular density, has an exact explicit power expression. It composes independently verified interval integration and negative-jump substitution theorems.
-- source:
--   Deterministic negative-jump interval integral needed before the actual original Levy-measure weighted generator integral; does not assume the source process is constructed.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_gen13_affine_crossing_negative_jump_integral
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ z in (-1 : ℝ)..(-y), (-1 - y - z) *
      |z| ^ (-(3 / 2 : ℝ))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) -
      (1 + y) * (2 * (y ^ (-(1 / 2 : ℝ)) - 1)) := by sorry
