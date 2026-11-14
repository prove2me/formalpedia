-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_disjoint_cell_step_bound
-- name    : AvramDividend.Classical.avram_chat24_disjoint_cell_step_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:34:24.050928+00:00
-- url     : https://prove2.me/theorems/cdab9258-d17e-47df-ba54-10b36cd4b1f1
-- title:
--   Measurable bounded steps on disjoint ordered cells
-- statement:
--   For arbitrary NNReal measure and strictly increasing grids, disjoint half-open cells transfer a uniform coefficient bound to the whole finite step function. Every step is a finite sum of constant measurable indicators. This is the finite-mesh part of parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b; proof draft preserved in p2m-drift-discrete-research.lean.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_disjoint_cell_step_bound
    (μ : Measure ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, StrictMono (u n))
    (c : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (n0 : ℕ)
    (hc : ∀ n, n0 ≤ n → ∀ i ∈ Finset.range (n + 1), ‖c n i‖ ≤ C) :
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then c n i else 0
      else 0
    (∀ n, AEStronglyMeasurable (G n) μ) ∧ (∀ n t, ‖G n t‖ ≤ C) := by sorry
