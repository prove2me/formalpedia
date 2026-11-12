-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB96_two_mesh_squared_step_pointwise
-- name    : AvramDividend.Classical.avram_gbB96_two_mesh_squared_step_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:59:38.549329+00:00
-- url     : https://prove2.me/theorems/5b6efa35-5160-498f-bc81-0b4a3160667e
-- title:
--   Original two-grid coefficient step-square diagonalisation on common refinement
-- statement:
--   For the identical original uniform grid coefficients G, the pointwise squared difference of the two step functions equals the sum of the squared coefficient differences on their product-refined mesh, at each positive interior time. This uses B91 to repeat both source grids and B92 to diagonalise the squared single-grid step sum. It is the exact analytic bridge into B82 without replacing X or D.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB91_one_mesh_step_indicator_refinement
import Theorems.Thm_AvramDividend_Classical_avram_gbB92_same_grid_step_product_diagonal
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB96_two_mesh_squared_step_pointwise
    {Ω : Type*} (n m p : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ) :
    let N : ℕ := (m + 1) * (p + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      (K m t ω - K p t ω) ^ 2 =
        (Finset.range N).sum (fun r =>
          if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
          then (G m (r / (p + 1)) ω -
                G p (r / (m + 1)) ω) ^ 2
          else 0) := by sorry
