-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB91_one_mesh_step_indicator_refinement
-- name    : AvramDividend.Classical.avram_gbB91_one_mesh_step_indicator_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:29:02.918036+00:00
-- url     : https://prove2.me/theorems/a0f6fb6f-695c-4b72-a264-380c9cd18fc1
-- title:
--   A coarse uniform-grid indicator step equals its repeated fine-grid step
-- statement:
--   Repeating each coefficient over b consecutive fine cells reproduces exactly the step function on the coarse uniform grid, including its right-open interval endpoint convention.
-- source:
--   Deterministic one-mesh partition child of original two-grid pointwise product B84.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB91_one_mesh_step_indicator_refinement
    {Ω : Type*} (n m b : ℕ) (hn : 0 < n) (hb : 0 < b)
    (G : ℕ → Ω → ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let δ : ℝ := (n : ℝ) / (((m + 1) * b : ℕ) : ℝ)
    ∀ t ∈ Ioo (0 : ℝ) (n : ℝ), ∀ ω : Ω,
      (Finset.range (m + 1)).sum (fun i =>
        if (((i : ℝ≥0) * D) : ℝ) ≤ t ∧
          t < ((((i : ℝ≥0) * D) + D : ℝ≥0) : ℝ)
        then G i ω else 0) =
      (Finset.range ((m + 1) * b)).sum (fun r =>
        if (r : ℝ) * δ ≤ t ∧ t < ((r + 1 : ℕ) : ℝ) * δ
        then G (r / b) ω else 0) := by sorry
