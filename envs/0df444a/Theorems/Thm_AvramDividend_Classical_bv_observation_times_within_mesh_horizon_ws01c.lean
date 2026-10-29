-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_observation_times_within_mesh_horizon_ws01c
-- name    : AvramDividend.Classical.bv_observation_times_within_mesh_horizon_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:56:41.170215+00:00
-- url     : https://prove2.me/theorems/b9c00caa-d2dd-437f-bbec-cdc4f6505731
-- title:
--   Each finite prefix grid observation lies within its final mesh horizon
-- statement:
--   All finite observations k h in the list k=0,...,M lie below M h, establishing the deterministic horizon bound used in the original-filtration grid stopping construction.
-- source:
--   Source-faithful preamble repair of failed authoring job 67e009c2-09b9-4a4b-b0b4-7bd42d0a1646 (unknown namespace AvramDividend.Classical); exact theorem statement unchanged. Proof work/avram_ws01c_observation_times_horizon_solution_repair_20261028.lean.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.bv_observation_times_within_mesh_horizon_ws01c
    (h : ℝ≥0) (M : ℕ) :
    ∀ t ∈ (List.range (M + 1)).map
        (fun k : ℕ => (k : ℝ≥0) * h),
      t ≤ (M : ℝ≥0) * h := by sorry
