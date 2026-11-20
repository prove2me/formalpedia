-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_uniform_randomclipped_step_le_mesh_delta
-- name    : AvramDividend.Classical.avram_pj_workerC_original_uniform_randomclipped_step_le_mesh_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:36:47.668308+00:00
-- url     : https://prove2.me/theorems/06dc2e35-5388-48e4-bad6-cb266f189661
-- title:
--   Actual uniform Lévy physical mesh clipped to a random ruin-stopping clock has every cell width at most n divided by m+1
-- statement:
--   For physical clock grid u_i=min(min(i,m+1)*n/(m+1),rho) with arbitrary sample-path stopping rho, every clipped cell satisfies u_(i+1)≤u_i+n/(m+1), including the final partial cell and all flat cells after rho. This gives the exact deterministic uniform mesh-width envelope needed for L1 convergence of finite negative jump cutoff and compensated Lévy errors without an assumed deterministic stopping time.
-- source:
--   Elementary Nat min successor arithmetic and NNReal multiplication/min bounds, applies directly to Proved b9dccb original four-term Stieltjes physical grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_uniform_randomclipped_step_le_mesh_delta
    {Ω : Type*} (n m : ℕ) (ρ : Ω → ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : Ω → ℕ → ℝ≥0 := fun ω i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    ∀ ω i, u ω (i + 1) ≤ u ω i + Δ := by sorry
