-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_intrinsic_threshold_invariance
-- name    : AvramDividend.Classical.avram_p2_l_mesh_intrinsic_threshold_invariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:33:26.042478+00:00
-- url     : https://prove2.me/theorems/bbd1d3d6-851d-4e9e-a60a-bc72e85d182c
-- title:
--   Intrinsic jump sum independent of significance threshold below test support
-- statement:
--   For the same original path and horizon, two finite intrinsic significant-jump sets selected at thresholds rho <= sigma yield identical marked-test sums if the test vanishes on real marks strictly above -sigma; no cutoff atom hypothesis is needed.

import Mathlib

open Set Filter Topology
open scoped NNReal BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_intrinsic_threshold_invariance
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ σ : ℝ) (hρσ : ρ ≤ σ)
    (f : ℝ → ℝ) (hf : ∀ z : ℝ, -σ < z → f z = 0)
    (Sρ Sσ : Finset ℝ≥0)
    (hSρ : ∀ u : ℝ≥0, u ∈ Sρ ↔ 0 < u ∧ u ≤ T ∧ ρ ≤ |Y u - Function.leftLim Y u|)
    (hSσ : ∀ u : ℝ≥0, u ∈ Sσ ↔ 0 < u ∧ u ≤ T ∧ σ ≤ |Y u - Function.leftLim Y u|) :
    (∑ u ∈ Sρ, f (Y u - Function.leftLim Y u)) =
      ∑ u ∈ Sσ, f (Y u - Function.leftLim Y u) := by sorry
