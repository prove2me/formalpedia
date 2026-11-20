-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
-- name    : AvramDividend.Classical.avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:05:47.316186+00:00
-- url     : https://prove2.me/theorems/1d1b7e8d-a292-4870-9fbb-3f5f2a27dbea
-- title:
--   Public quadratic ruin-clipped positive-reserve second derivative equals two
-- statement:
--   For the original piecewise quadratic spectrally-negative dividend HJB test function w=0 on negative reserves and 1+y+y² on nonnegative reserves, the classical second derivative at every strictly positive reserve equals two. This directly supplies the continuous Gaussian generator term without importing private per-mission helper theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_public_positive_quadratic_ruinclipped_second_derivative
    (y : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun z : ℝ =>
      if z < 0 then 0 else 1 + z + z ^ 2) y = 2 := by sorry
