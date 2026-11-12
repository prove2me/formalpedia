-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB84_two_grid_step_product_refinement_pointwise
-- name    : AvramDividend.Classical.avram_gbB84_two_grid_step_product_refinement_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:54:15.23621+00:00
-- url     : https://prove2.me/theorems/08f53ba2-88b2-43d7-98be-590626a88108
-- title:
--   Pointwise product of two deterministic-grid steps is the common-refinement step
-- statement:
--   For times strictly between zero and n, each coarse uniform-mesh step selects one coefficient, and their product is exactly the fine common-refinement step with coefficient product at the corresponding coarse indices. This is a pathwise deterministic identity with no probabilistic hypotheses.
-- source:
--   Algebraic interval-partition child of original two-grid step time-integral B78.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB84_two_grid_step_product_refinement_pointwise
    {Ω : Type*} (n m l : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ) :
    let N : ℕ := (m + 1) * (l + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      K m t ω * K l t ω =
        (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then G m (r / (l + 1)) ω * G l (r / (m + 1)) ω
          else 0) := by sorry
