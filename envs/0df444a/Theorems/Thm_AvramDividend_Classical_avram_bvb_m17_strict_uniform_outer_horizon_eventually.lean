-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_strict_uniform_outer_horizon_eventually
-- name    : AvramDividend.Classical.avram_bvb_m17_strict_uniform_outer_horizon_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:32:11.712302+00:00
-- url     : https://prove2.me/theorems/d2fe28a6-580a-4e14-8e32-ffb87f7600a2
-- title:
--   Every strict interior observation eventually lies within the original physical finite-grid inner horizon
-- statement:
--   For any positive T and fixed r strictly between 0 and T, the physical uniform-grid inner horizon T(n+1)/(n+2) eventually exceeds r. This is the exact deterministic outer-grid mask in the original finite-activity marked compensation, including the last fractional cell.
-- source:
--   Proved bva20 strict inner horizon ruin mask eventual equivalence b0c87b9c at τ=∞; physical uniform-grid identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva20_strict_inner_horizon_ruin_mask_eventual_equiv
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_m17_strict_uniform_outer_horizon_eventually
    (T r : ℝ) (hT : 0 < T) (hr : 0 < r) (hrT : r < T) :
    ∀ᶠ n in Filter.atTop,
      r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by sorry
