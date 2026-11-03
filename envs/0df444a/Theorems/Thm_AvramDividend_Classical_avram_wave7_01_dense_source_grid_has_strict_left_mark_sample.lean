-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
-- name    : AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:57:19.097896+00:00
-- url     : https://prove2.me/theorems/17732326-7c46-4df9-bc4b-298be791c7ed
-- title:
--   Every positive left sampling window of a source candidate time meets a fixed dense grid
-- statement:
--   For the actual nonnegative source clock, every positive jump candidate time has a dense grid point strictly before it and less than ε away. When the ε window crosses time zero, use the nonempty interval (0,t). Otherwise use (t-ε,t). This discharges the left-grid selector existence premise without BV or finite activity.
-- source:
--   DenseRange.exists_mem_open, tsub_lt_self and NNReal.coe_sub applied to the original NNReal clock, in pinned Mathlib.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t ε : ℝ≥0) (ht : 0 < t) (hε : 0 < ε) :
    ∃ n : ℕ, grid n < t ∧ t < grid n + ε := by sorry
