-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
-- name    : AvramDividend.Classical.avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:14:36.871288+00:00
-- url     : https://prove2.me/theorems/4d58f2a1-b610-41a8-8ccf-88381cbec2eb
-- title:
--   Uniform original physical grid finite negative-mark compensated intensity rate budget
-- statement:
--   For any finite stopped horizon n and refinement m, m original physical grid cells of width n/(m+1) each with a fixed nonnegative finite negative-mark Lévy intensity R have total expected rate at most nR, uniformly in m. This is the exact rate sum budget needed with a stopped marked compensator diagonal L2 isometry.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_finite_mark_physical_grid_rate_uniform_bound
    (n m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (∑ _i ∈ Finset.range m,
      ((n : ℝ) / ((m : ℝ) + 1)) * R) ≤
      (n : ℝ) * R := by sorry
