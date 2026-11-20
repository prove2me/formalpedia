-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
-- name    : AvramDividend.Classical.avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:36:06.970157+00:00
-- url     : https://prove2.me/theorems/0cdd8cee-1869-48fe-ae1f-1b4bb0e66fd2
-- title:
--   Every randomly clipped physical stop cell is no longer than its deterministic mesh step, including the final partial stopping cell
-- statement:
--   If adjacent un-clipped deterministic NNReal physical grid times grow by at most mesh width Delta, then every stopped random-clock clipped cell u_i=min(g_i,rho) grows by at most Delta, for every path and cell including the one crossing rho. This is required to pass deterministic-grid stopped negative-mark compensation and C2 tail estimates to the exact partially clipped final cell.
-- source:
--   Elementary NNReal min monotonicity and step bound; supports original b9dccb finite physical Stieltjes mesh and 7687813e stopped-grid mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_stopped_physical_cell_step_le_unclipped_mesh
    {Ω : Type*} (g : ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (Δ : ℝ≥0) (hStep : ∀ i, g (i+1) ≤ g i + Δ) :
    ∀ ω i, min (g (i+1)) (ρ ω) ≤ min (g i) (ρ ω) + Δ := by sorry
