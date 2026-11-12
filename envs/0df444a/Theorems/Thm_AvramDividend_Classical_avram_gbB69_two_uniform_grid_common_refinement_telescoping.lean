-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB69_two_uniform_grid_common_refinement_telescoping
-- name    : AvramDividend.Classical.avram_gbB69_two_uniform_grid_common_refinement_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:55:54.577695+00:00
-- url     : https://prove2.me/theorems/188ce548-6829-4709-9ef0-e7643ceddb00
-- title:
--   Common refinement of two uniform grids with arbitrary path and two predictable coefficients
-- statement:
--   For any real-valued path, arbitrary grid coefficients, and drift, the difference between two discounted uniform-grid linear increment sums equals the sum over their common refinement with each coefficient repeated across its fine cells. This is a purely algebraic telescoping and rational-grid indexing identity, reusable in the original Gaussian two-grid L2 bound.
-- source:
--   Avram Gaussian B, 11 November 2026. Pure original-grid deterministic telescoping step for gbB60.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB69_two_uniform_grid_common_refinement_telescoping
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (n m p : ℕ) (G : ℕ → ℕ → Ω → ℝ) :
    let L : ℕ → Ω → ℝ := fun h ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((h + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (h + 1)).sum (fun i =>
        G h i ω * (X (s i + Δ) ω - X (s i) ω - (Δ : ℝ) * c))
    let N : ℕ := (m + 1) * (p + 1)
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun r => (r : ℝ≥0) * Δ
    ∀ ω, L m ω - L p ω =
      (Finset.range N).sum (fun r =>
        (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) *
          (X (s r + Δ) ω - X (s r) ω - (Δ : ℝ) * c)) := by sorry
