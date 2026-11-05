-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_physical_grid_real_rate_bridge
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_physical_grid_real_rate_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:57:47.066201+00:00
-- url     : https://prove2.me/theorems/4829bfa1-dde5-45fb-ad3a-5c6627056bfa
-- title:
--   Original physical uniform NNReal endpoints have exactly the accepted real triangular chronological rate
-- statement:
--   For the exact original physical NNReal grid endpoints, their real past-by-cell Lévy-rate sum equals the deterministic real triangular scalar, with the true source clock T. The proof imports the independently Proved endpoint and real rate identity; no stochastic distribution change.
-- source:
--   Proved 6bdc2c26 uniform source grid endpoints and 44077ce5 exact real triangular rate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
open AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_physical_grid_real_rate_bridge
    (T a : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∑ i : Fin k, ((s i : ℝ) * (a : ℝ)) *
      (((t i - s i : ℝ≥0) : ℝ) * (a : ℝ))) =
      ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := by sorry
