-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_local_scale_deriv_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T08:55:51.855766+00:00
-- url     : https://prove2.me/theorems/551f0a4b-4af7-4930-ba09-1cc938f352bc
-- title:
--   Smooth fit from local scale differentiability and positive derivative
-- statement:
--   At a positive barrier, differentiability of the scale at that point and positivity of its derivative suffice to paste the left scale-ratio and right affine branches with ordinary derivative one.
-- source:
--   Extracted deterministic join case from Proved vcstar_deriv_ge_one_of_regular_minimal.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.TangentCone.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_deriv_one_of_local_scale_deriv_positive
    (W : ℝ → ℝ) (hcpos : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hdpos : 0 < deriv W (cstar W).toReal) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
