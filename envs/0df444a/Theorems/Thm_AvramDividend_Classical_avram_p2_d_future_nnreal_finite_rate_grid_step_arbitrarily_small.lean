-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small
-- name    : AvramDividend.Classical.avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:53:44.594082+00:00
-- url     : https://prove2.me/theorems/73ee1057-d066-49c4-ac8a-aeb932c68b4f
-- title:
--   The finite unit-time rate contribution of one rational time-grid cell can be made arbitrarily small
-- statement:
--   For any finite nonnegative scalar rate c and any strictly positive error tolerance ε in NNReal, choose a positive natural time-grid denominator d so the one-cell rate contribution c/d is smaller than ε. This is the Archimedean limiting ingredient for promoting the original source rational marked-count mean sandwich into an all-real-time linearity equality on finite-rate mark sets.
-- source:
--   Archimedean NNReal: choose d>c/ε by exists_nat_gt, then divide the resulting c<dε by d. Supports the original source mean mesh theorem dervied from 659c56d0 and 1b0514e9. No ν identification or process change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_nnreal_finite_rate_grid_step_arbitrarily_small
    (c ε : ℝ≥0) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ c / (d : ℝ≥0) < ε := by sorry
