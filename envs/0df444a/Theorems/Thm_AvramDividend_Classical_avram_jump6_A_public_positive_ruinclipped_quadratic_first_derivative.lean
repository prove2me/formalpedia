-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
-- name    : AvramDividend.Classical.avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:08:46.128145+00:00
-- url     : https://prove2.me/theorems/1e6d1935-eb63-40b9-8967-5afb9aae643d
-- title:
--   Public positive-reserve first derivative of quadratic ruin-clipped HJB function
-- statement:
--   The original piecewise quadratic function has derivative 1+2y and gradient at least one for every positive reserve. Provides public formal Gaussian HJB gradient source without private imported premises.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_public_positive_ruinclipped_quadratic_first_derivative
    (y : ℝ) (hy : 0 < y) :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else 1 + z + z ^ 2
    deriv w y = 1 + 2 * y ∧ 1 ≤ deriv w y := by sorry
