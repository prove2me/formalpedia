-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
-- name    : AvramDividend.Classical.avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:07:13.65432+00:00
-- url     : https://prove2.me/theorems/35322394-5ff4-4183-a466-a5dea847e463
-- title:
--   Original finite stopped marked-grid each-cell L2 gives every cross-cell compensated increment product integrable
-- statement:
--   For any finite set of actual stopped physical-grid compensated negative-mark increments, if each one belongs to L2 in the original measure space then every pairwise product is integrable. This is the Hölder inequality integrability condition for the exact finite-grid cross-cell orthogonality isometry.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_marked_grid_L2_each_cell_implies_all_cross_products_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ∈ s, MemLp (Z i) 2 P) :
    ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P := by sorry
