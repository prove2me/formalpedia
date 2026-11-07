-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
-- name    : AvramDividend.Classical.avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:38:44.610811+00:00
-- url     : https://prove2.me/theorems/1a11ea95-5e6c-4572-99f1-9c4b130a6c18
-- title:
--   Nonnegative Fatou liminf survives a scalar source error discount tending to one
-- statement:
--   This fixes v1's missing ENNReal scoped notation. For an extended-real scalar a_n tending to one, the standard nonnegative liminf product inequality gives liminf u_n <= liminf(a_n u_n). It is used in genuine signed original BV source slack normalisation.

import Mathlib
open Filter MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_ennreal_liminf_scaled_tendsto_one
    (u a : ℕ → ℝ≥0∞)
    (ha : Filter.Tendsto a Filter.atTop (nhds (1 : ℝ≥0∞))) :
    liminf u Filter.atTop ≤
      liminf (fun n => a n * u n) Filter.atTop := by sorry
