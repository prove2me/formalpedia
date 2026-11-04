-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_real_rate_mesh_sum
-- name    : AvramDividend.Classical.avram_p2_34dbea70_uniform_real_rate_mesh_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:09:27.764196+00:00
-- url     : https://prove2.me/theorems/7fef0aa4-de9a-4524-81d7-c3bf0831212a
-- title:
--   Original-grid ENNReal ofReal cell-rate sum is C times horizon
-- statement:
--   For any NNReal horizon T, nonnegative real C and resolution n, sum ENNReal.ofReal(C*T/(n+1)) over the n+1 uniform grid cells. The result equals ENNReal.ofReal(C*T). The identity uses the proved exact NNReal width sum and pinned ofReal multiplication/cast identities. It exactly matches the source original Lévy negative-tail grid-mean upper bound.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_original_grid_width_sum

open AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_uniform_real_rate_mesh_sum
    (T : ℝ≥0) (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    (∑ _i ∈ Finset.range (n + 1),
      ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))) =
        ENNReal.ofReal (C * (T : ℝ)) := by sorry
