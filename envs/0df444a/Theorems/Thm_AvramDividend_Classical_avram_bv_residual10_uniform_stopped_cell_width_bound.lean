-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_uniform_stopped_cell_width_bound
-- name    : AvramDividend.Classical.avram_bv_residual10_uniform_stopped_cell_width_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:29:31.82993+00:00
-- url     : https://prove2.me/theorems/cfdaf927-f281-45eb-8501-9238b44fc49c
-- title:
--   Clipping original uniform physical-grid cells at a stopped clock cannot increase their widths
-- statement:
--   If each original physical-grid endpoint is T times its index divided by n plus two with positive horizon, then clipping both endpoints to any common real stopping clock produces a nonnegative increment no larger than one original grid cell. This deterministic time-clipping inequality is uniform in row and cell index and applies in particular to the authentic dividend-dependent ruin-clock truncation after its nonnegative-real coercion. It does not strengthen or substitute the original stochastic process assumptions.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, deterministic stopped physical mesh geometry, 7 November 2026

import Mathlib

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_uniform_stopped_cell_width_bound
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (s : ℝ) :
    ∀ n i : ℕ,
      0 ≤ min (u n (i + 1) : ℝ) s - min (u n i : ℝ) s ∧
      min (u n (i + 1) : ℝ) s - min (u n i : ℝ) s ≤
        T / ((n : ℝ) + 2) := by sorry
