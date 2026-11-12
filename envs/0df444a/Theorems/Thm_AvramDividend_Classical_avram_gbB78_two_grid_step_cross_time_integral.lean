-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB78_two_grid_step_cross_time_integral
-- name    : AvramDividend.Classical.avram_gbB78_two_grid_step_cross_time_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:59:39.966515+00:00
-- url     : https://prove2.me/theorems/993b71ac-f20d-475f-a1c1-c2e4f60dcfbe
-- title:
--   Deterministic two-grid step coefficients have exact overlap time integral on common refinement
-- statement:
--   For two bounded measurable deterministic-grid step coefficient families, integration of their expected pointwise product over the finite horizon equals the common-cell width times the finite sum of expected products at the two coarse-grid indices. The common refinement has (m+1)(l+1) cells and handles arbitrary unrelated uniform meshes.
-- source:
--   Deterministic Lebesgue time-integral atom for generic original Gaussian two-grid covariance gbB76; separate from stochastic orthogonality gbB77.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB78_two_grid_step_cross_time_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (n m l : ℕ) (hn : 0 < n)
    (G : ℕ → ℕ → Ω → ℝ)
    (hG : ∀ a i, StronglyMeasurable (G a i))
    (hBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ a i ω, |G a i ω| ≤ B) :
    let N : ℕ := (m + 1) * (l + 1)
    let δ : ℝ := (n : ℝ) / (N : ℝ)
    let K : ℕ → ℝ → Ω → ℝ := fun k t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      (Finset.range (k + 1)).sum (fun i =>
        if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
        then G k i ω else 0)
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, K m t ω * K l t ω ∂P) ∂volume) =
      δ * (Finset.range N).sum (fun r =>
        ∫ ω, G m (r / (l + 1)) ω *
          G l (r / (m + 1)) ω ∂P) := by sorry
