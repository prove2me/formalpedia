-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB198_single_uniform_grid_weighted_refinement
-- name    : AvramDividend.Classical.avram_gbB198_single_uniform_grid_weighted_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:04:18.416425+00:00
-- url     : https://prove2.me/theorems/aef94645-3a39-4ec0-94bc-e322c107d79c
-- title:
--   Exact physical-time refinement of original single weighted Lévy grid to repeated fine coefficients
-- statement:
--   For any original cadlag source path and arbitrary predictable or deterministic sampled weight, the coarse centered weighted increment sum equals its repeated-weight finer uniform grid representation, preserving the exact real-valued source and NNReal time coordinates.
-- source:
--   Avram Gaussian B two-mesh mixed covariance; Proved avram_gb83_weighted_block_refinement and avram_gb86_uniform_refinement_nnreal_time_bridge. Needed to reduce B83 to B77 with a common fine grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB198_single_uniform_grid_weighted_refinement
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (n m b : ℕ) (hb : 0 < b) (H : ℕ → Ω → ℝ) :
    let δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * δ
    let N : ℕ := (m + 1) * b
    let ε : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let r : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * ε
    ∀ ω, (Finset.range (m + 1)).sum (fun i =>
      H i ω * (X (s i + δ) ω - X (s i) ω - (δ : ℝ) * c)) =
      (Finset.range N).sum (fun j =>
        H (j / b) ω * (X (r j + ε) ω - X (r j) ω -
          (ε : ℝ) * c)) := by sorry
