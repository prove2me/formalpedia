-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_source_quad_regularity
-- name    : AvramDividend.Classical.avram_gbB30_original_source_quad_regularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:34:28.236481+00:00
-- url     : https://prove2.me/theorems/1862c542-19fd-4fd2-8ba3-05ed8fc304cc
-- title:
--   Exact source reward continuity, negative support and ENNReal-cap C2
-- statement:
--   Derive exactly the source hypotheses w0, continuity on nonnegative reserves, zero below zero and C2 on the actual ENNReal cap interior from the proven local smoothness and the pinned ENNReal.ofReal order equivalence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_quadratic_cap_smoothness
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_original_source_quad_regularity :
    0 ≤ (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) 0 ∧
      ContinuousOn (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) (Ici 0) ∧
      (∀ y : ℝ, y < 0 → (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y = 0) ∧
      ContDiffOn ℝ 2 (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y <
          ENNReal.ofReal (1 / 8 : ℝ)} := by sorry
