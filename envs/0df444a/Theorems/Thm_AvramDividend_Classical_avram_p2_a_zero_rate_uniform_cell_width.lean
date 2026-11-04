-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:50.184149+00:00
-- url     : https://prove2.me/theorems/d7346150-dbde-456c-9f5d-2bbd1bfafaca
-- title:
--   Exact stationary width of any original nonnegative uniform-grid cell
-- statement:
--   On the original NNReal time domain, the time difference between consecutive equispaced endpoints (j+1)δ and jδ is exactly δ, including at δ=0. This is the deterministic time-domain identity required to collapse the original stationary-grid mean sum into (n+1) times one genuine source-increment event probability; it uses no rate or compensator hypothesis.

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_width
    (j : ℕ) (δ : ℝ≥0) :
    (((j + 1 : ℕ) : ℝ≥0) * δ) - ((j : ℝ≥0) * δ) = δ := by sorry
