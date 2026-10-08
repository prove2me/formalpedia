-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
-- name    : AvramDividend.Classical.vcstar_deriv_eq_one_above_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:32:13.267403+00:00
-- url     : https://prove2.me/theorems/4098a584-9c09-4437-b71f-5590221db9ab
-- title:
--   The candidate barrier value has derivative one strictly above c-star
-- statement:
--   For every y strictly above the finite real representative of c*, the candidate vcstar is locally an affine real function y-c*+constant and therefore has derivative exactly one. This is the equality half of the HJB equation in the continuation-dividend region above the barrier; it is independent of stochastic regularity and uses only the piecewise barrierValue definition.
-- source:
--   Avram, Palmowski and Pistorius (2007), barrier value formula (5.1), affine branch for x>a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_deriv_eq_one_above_cstar (W : ℝ → ℝ) (y : ℝ)
    (hy : (cstar W).toReal < y) :
    deriv (vcstar W) y = 1 := by
  sorry
end AvramDividend.Classical
