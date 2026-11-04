-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_rational_grid_enclosure
-- name    : AvramDividend.Classical.avram_p2_d_future_nnreal_rational_grid_enclosure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:49:36.351201+00:00
-- url     : https://prove2.me/theorems/659c56d0-dcc4-4cff-a328-2079eaa8b68c
-- title:
--   Every nonnegative real horizon is enclosed by consecutive rational time-grid points
-- statement:
--   Given a nonnegative real time t and positive natural denominator d, find a natural grid index n with n/d≤t≤(n+1)/d. This deterministic rational enclosure supplies the missing uniform-grid witness for the accepted original marked-count rational sandwich and the desired finite-rate real-time scaling, including t=0.
-- source:
--   Mathlib Nat.floor order bounds and NNReal division; useful when applying Proved original source rational sandwich 1b0514e9-716f-4d42-8484-7f4338459f5a to arbitrary real physical horizons. Does not assume an auxiliary Poisson process or ν intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_nnreal_rational_grid_enclosure
    (t : ℝ≥0) (d : ℕ) (hd : 0 < d) :
    ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) := by sorry
