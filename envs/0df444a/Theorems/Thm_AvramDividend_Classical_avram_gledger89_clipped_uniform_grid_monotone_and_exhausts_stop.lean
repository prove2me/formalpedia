-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
-- name    : AvramDividend.Classical.avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:03:33.379785+00:00
-- url     : https://prove2.me/theorems/7a513525-6989-4f7d-8a74-f95ea7a4c926
-- title:
--   Original physical clipped uniform mesh is monotone and exhausts its bounded stopping clock
-- statement:
--   For any bounded original stopped clock rho and mesh width n/(m+2), the capped grid v_i=min(i*delta,rho) is monotone, starts at zero, and reaches exactly rho at its final index m+2. This is the finite-grid hypothesis needed for the exact cash partition gledger88 in the gledger81 original Gaussian contact estimate.
-- source:
--   Original deterministic clipped grid endpoint and monotonicity needed to combine gledger88 cash partition with gledger83/85 in gledger81 16e988d7.

import Mathlib
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
    (n m : ℕ) (ρ : ℝ≥0) (hρ : ρ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    Monotone v ∧ v 0 = 0 ∧ v (m + 2) = ρ := by sorry
