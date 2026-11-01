-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_prejump_fractional_left_time_mesh
-- name    : AvramDividend.Classical.avram_wave4_04b_prejump_fractional_left_time_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:18:29.583016+00:00
-- url     : https://prove2.me/theorems/ebc2b859-2717-485f-baa8-296649c2d8db
-- title:
--   Measurable strictly pre-jump fractional time mesh converges to every positive observation time
-- statement:
--   For every n, the deterministic time retraction c_n(t)=t−t2^{−n−1} is Borel measurable. For every t it converges to t, and at each positive t it stays strictly to the left. This source-free mesh is an actual usable witness for Borel measurability of strict-left-limit controlled finite-variation paths and pre-jump reserve integrands, not a fixed-time marginal approximation.
-- source:
--   Explicit fractional-from-below measurable maps and geometric limit; separates the nontrivial strict pre-jump mesh from the controlled left-limit measurability proof.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_prejump_fractional_left_time_mesh :
    (∀ n : ℕ, Measurable
      (fun t : ℝ≥0 => t - t * (1 / 2 : ℝ≥0) ^ (n + 1))) ∧
    (∀ t : ℝ≥0, Tendsto
      (fun n : ℕ => t - t * (1 / 2 : ℝ≥0) ^ (n + 1))
      atTop (𝓝 t)) ∧
    (∀ t : ℝ≥0, 0 < t → ∀ n : ℕ,
      t - t * (1 / 2 : ℝ≥0) ^ (n + 1) < t) := by
  sorry
