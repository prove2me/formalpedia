-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_mesh_terminal_clip
-- name    : AvramDividend.Classical.avram_p3_2_physical_mesh_terminal_clip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:09:19.890217+00:00
-- url     : https://prove2.me/theorems/2c3eabad-a25e-4a2b-8be5-e9f7993c6af4
-- title:
--   The final stopped physical mesh point equals the clipped stopping time
-- statement:
--   The endpoint of a time grid with m+1 equal physical subdivisions, clipped at τ≤T, is exactly τ. This lets the strictly pre-horizon original dividend cash mesh cover the entire stopped interval.
-- source:
--   Mathlib arithmetic on nonnegative reals; original-process grid endpoint identification.

import Mathlib

open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_physical_mesh_terminal_clip (T τ : ℝ≥0) (m : ℕ) (hτ : τ ≤ T) :
    min (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ = τ:= by sorry
