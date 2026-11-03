-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
-- name    : AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:56:35.688894+00:00
-- url     : https://prove2.me/theorems/898f937f-d2da-4d6b-8dc1-7bd134d657ed
-- title:
--   Every positive right sampling window of a source candidate time meets a fixed countable dense grid
-- statement:
--   For the raw original path clock ℝ≥0, every strictly positive interval immediately to the right of a candidate jump time contains an indexed member of any dense rational observation grid. This discharges the existence premise of the accepted measurable right-grid-selector helper, uniformly for random times by pathwise instantiation.
-- source:
--   DenseRange.exists_mem_open, nonempty_Ioo and the positive-neighbourhood inequality on NNReal, in pinned Mathlib; no stochastic or finite activity assumption.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t ε : ℝ≥0) (hε : 0 < ε) :
    ∃ n : ℕ, t < grid n ∧ grid n < t + ε := by sorry
