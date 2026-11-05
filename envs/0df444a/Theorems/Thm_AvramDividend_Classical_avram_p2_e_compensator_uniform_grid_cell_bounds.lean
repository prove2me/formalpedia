-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_cell_bounds
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_cell_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:54:05.417924+00:00
-- url     : https://prove2.me/theorems/38bdd935-373f-4713-8025-1bc568be1a16
-- title:
--   Physical uniform grid cells are chronologically ordered and contained in the original horizon
-- statement:
--   The start and end of each uniform half-open physical time cell satisfy s_i≤t_i≤T, including at zero horizon. This supplies the domain hypotheses for source one-cell jump-count cardinality and expectation theorems.
-- source:
--   Deterministic uniform physical time grid, pinned Fin bounded indices and NNReal ordered division; intended for original stopped negative-band count source identities.

import Mathlib

open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_cell_bounds (T : ℝ≥0) (k : ℕ) (i : Fin (k + 1)) :
    (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1)) ≤
        (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1))) ∧
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1))) ≤ T := by sorry
