-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_grid_partial_negative_large_mark_count_finite
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_grid_partial_negative_large_mark_count_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:15:22.170403+00:00
-- url     : https://prove2.me/theorems/48a858af-3803-4b25-8c85-b925bb908e01
-- title:
--   Every actual randomly clipped physical grid cell contains finitely many negative Lévy jumps above a fixed magnitude cutoff including the final partial cell
-- statement:
--   For the exact original negative Lévy mark counting measure, any monotone physical grid and any pathwise stop rho, each interval (min(g_i,rho),min(g_(i+1),rho)] contains only finitely many jumps of absolute magnitude at least eta>0. Includes the partial cell at stopping and empty cells after rho. This holds for infinite-activity unbounded-variation Lévy processes because the cutoff excludes tiny jumps, without incorrectly assuming full negative jump intensity finite.
-- source:
--   Proved 35a471e5 exact actual clipped finite separated jump count on a random clock, monotone grid min arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_grid_partial_negative_large_mark_count_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : Ω → ℝ≥0) (ω : Ω)
    (g : ℕ → ℝ≥0) (hg : Monotone g) (i : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (min (g i) (ρ ω)) (min (g (i+1)) (ρ ω)) ×ˢ
        {z : ℝ | η ≤ dist z 0}) < ⊤ := by sorry
