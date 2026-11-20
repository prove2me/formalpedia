-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_horizon_discount_rate_dominates_mesh_rate
-- name    : AvramDividend.Classical.avram_jump6_B_original_positive_horizon_discount_rate_dominates_mesh_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:31:28.477114+00:00
-- url     : https://prove2.me/theorems/9bd30c26-c92f-4df4-8879-c138493b9930
-- title:
--   Positive horizon discount multiplier dominates the exact original physical mesh rate
-- statement:
--   For q>0 and positive integer horizon n, the source-level ruin-contact error coefficient q*n*exp(q*n)/(j+1) dominates the exact strict original physical grid error q/(j+1) for any mesh j. This is the scalar rate comparison required when upgrading the strict prefix source to the original ruin-contact parent.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_positive_horizon_discount_rate_dominates_mesh_rate
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (j : ℕ) :
    q / ((j + 1 : ℕ) : ℝ) ≤
      q * ((n : ℝ) / ((j + 1 : ℕ) : ℝ)) *
        Real.exp (q * (n : ℝ)) := by sorry
