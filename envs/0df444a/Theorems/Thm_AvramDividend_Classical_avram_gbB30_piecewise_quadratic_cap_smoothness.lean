-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_quadratic_cap_smoothness
-- name    : AvramDividend.Classical.avram_gbB30_piecewise_quadratic_cap_smoothness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T13:33:41.666035+00:00
-- url     : https://prove2.me/theorems/e38f773b-b16b-43fc-a89b-68842fb0a8bb
-- title:
--   Original piecewise quadratic source continuity and cap interior C2
-- statement:
--   For the sigma-1 Gaussian source reward w(y)=0 below zero and w(y)=2y-4y² otherwise, verify continuity on all nonnegative reserves, smoothness C2 on the cap interior (0,1/8), and vanishing reward below zero. This matches source regularity assumptions without extending differentiability across zero.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB30_piecewise_quadratic_cap_smoothness :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else 2 * z - 4 * z ^ 2
    ContinuousOn w (Ici 0) ∧
      ContDiffOn ℝ 2 w (Ioo 0 (1 / 8 : ℝ)) ∧
      w 0 = 0 ∧ (∀ y : ℝ, y < 0 → w y = 0) := by sorry
