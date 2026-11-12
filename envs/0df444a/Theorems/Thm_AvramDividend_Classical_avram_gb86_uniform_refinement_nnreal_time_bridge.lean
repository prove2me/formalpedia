-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb86_uniform_refinement_nnreal_time_bridge
-- name    : AvramDividend.Classical.avram_gb86_uniform_refinement_nnreal_time_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:19:42.947197+00:00
-- url     : https://prove2.me/theorems/68d47d39-ea4a-4e9a-a0f6-0ac0e7f47835
-- title:
--   Uniform original-time grid aligns with its product refinement
-- statement:
--   For a coarse grid of m+1 intervals and a product refinement by b positive subintervals, the original NNReal time at coarse cell i equals the fine-grid time at index i*b. This exact time equality connects the weighted finite-sum telescoping identity gb83 to the original-path two-grid stochastic sum gb82.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb86_uniform_refinement_nnreal_time_bridge
    (n m b i : ℕ) (hb : 0 < b) :
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) =
    ((i * b : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)) := by sorry
