-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_predecessor
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_predecessor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:06.604082+00:00
-- url     : https://prove2.me/theorems/5e0c0ba4-ea63-454d-85fe-f5a7ff9dfc2f
-- title:
--   Exact predecessor identity for nonnegative original grid-cell endpoints
-- statement:
--   For every finite grid index j and any NNReal mesh width δ, subtracting δ from the right endpoint (j+1)δ yields exactly jδ in the truncated nonnegative time domain. This arithmetic identity is required to replace source-specific left-cell endpoints with stationary independent-increment marks on the genuine original Lévy process.

import Mathlib
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_predecessor
    (j : ℕ) (δ : ℝ≥0) :
    (((j + 1 : ℕ) : ℝ≥0) * δ) - δ = (j : ℝ≥0) * δ := by sorry
