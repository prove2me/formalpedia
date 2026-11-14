-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_uniform_prefix_strictly_precedes_full_horizon
-- name    : AvramDividend.Classical.avram_bvb24_original_uniform_prefix_strictly_precedes_full_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:25:39.969506+00:00
-- url     : https://prove2.me/theorems/0faa9137-ee29-44ff-80ac-870bffe623a6
-- title:
--   Original finite-horizon physical uniform prefix always remains strictly below observation horizon in extended nonnegative clock
-- statement:
--   For a strictly positive original physical observation horizon, each uniform finite-grid prefix endpoint is strictly less than that horizon, even after both endpoints are embedded in the original extended nonnegative time order. Consequently, the original source ruin clock equal to the horizon is excluded by every strict clipped-prefix endpoint; the actual horizon terminal/contact case requires its own argument, whereas ruin strictly before the horizon is eventually included.
-- source:
--   Pinned Mathlib ENNReal.ofReal_lt_ofReal_iff and positivity of physical grid width; exact original grid in b0915396 and ruin-at-horizon child 983bff50.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_uniform_prefix_strictly_precedes_full_horizon
    (T : ℝ) (hT : 0 < T) (n : ℕ) :
    ENNReal.ofReal (T - T / ((n : ℝ) + 2)) <
      ENNReal.ofReal T := by sorry
