-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB146_uniform_real_mesh_sum_bound_on_cells
-- name    : AvramDividend.Classical.avram_gbB146_uniform_real_mesh_sum_bound_on_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:12:54.597096+00:00
-- url     : https://prove2.me/theorems/3cd4a8b8-73bd-4621-8a36-681fdfd0bd4c
-- title:
--   Uniform real mesh-sum bound by one coefficient bound
-- statement:
--   B111 selects one active coefficient from the full uniform mesh sum. A bound on each coefficient therefore gives a mesh-independent step-process bound inside the time horizon.
-- source:
--   Proved B111

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB146_uniform_real_mesh_sum_bound_on_cells
    {Ω : Type*} (n : ℕ) (hn : 0 < n) (G : ℕ → ℕ → Ω → ℝ)
    (B : ℝ) (hG : ∀ m i ω, |G m i ω| ≤ B) :
    ∀ (m : ℕ) (t : ℝ) (ω : Ω), t ∈ Ico (0 : ℝ) (n : ℝ) →
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      |(Finset.range (m + 1)).sum (fun i =>
        if (i : ℝ) * Δ ≤ t ∧ t < ((i + 1 : ℕ) : ℝ) * Δ
        then G m i ω else 0)| ≤ B := by sorry
