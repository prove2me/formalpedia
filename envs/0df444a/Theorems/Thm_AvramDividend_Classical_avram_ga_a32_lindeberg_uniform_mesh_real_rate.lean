-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a32_lindeberg_uniform_mesh_real_rate
-- name    : AvramDividend.Classical.avram_ga_a32_lindeberg_uniform_mesh_real_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:14:26.678197+00:00
-- url     : https://prove2.me/theorems/27ea6fc5-6526-4175-8d01-4ef938d9652f
-- title:
--   Gaussian physical uniform mesh fourth moment sum decays at order one over cell count
-- statement:
--   Over m full cells of width n/(m+1), the deterministic Gaussian fourth-moment mesh bound is at most three times the squared horizon divided by m+1.
-- source:
--   Uniform-grid deterministic rate required to apply original Gaussian expected large-increment energy ga_a31 in b0d9951c.

import Mathlib

theorem AvramDividend.Classical.avram_ga_a32_lindeberg_uniform_mesh_real_rate (n m : ℕ) :
    (∑ _i ∈ Finset.range m,
      (3 : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2) ≤
      3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1) := by sorry
