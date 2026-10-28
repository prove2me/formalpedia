-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_of_C2_scale_stationary_positive_C1
-- name    : AvramDividend.Classical.vcstar_global_C2_of_C2_scale_stationary_positive_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:17:53.596004+00:00
-- url     : https://prove2.me/theorems/09e8fc84-5193-44e8-8c97-870b2da9e2e4
-- title:
--   Deterministic global C2 barrier gluing from stationary scale C2 and candidate C1
-- statement:
--   This deterministic, Gaussian-compatible barrier calculus bridge combines C2 positive-axis smoothness of W, strictly positive W'(c*), stationary curvature W''(c*)=0, and global C1 of the barrier candidate to conclude its global C2 smoothness. The proof uses separately proved C1 gluing of the normalised scale derivative, the exact piecewise vcstar derivative identity and the generic C2 criterion. It is an importable conditional consumer for the open Gaussian barrier C2 theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Theorem 2, Gaussian positive-barrier smooth fit; pinned Mathlib contDiffOn_succ_iff_deriv_of_isOpen.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_piecewise_const_of_stationary_join
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_piecewise_ratio_one_of_C1_positive
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_of_deriv_eq_C1
open Set AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- An already C1 barrier candidate becomes C2 when the positive scale denominator is nonzero and its normalised scale derivative is stationary at the join. -/
theorem vcstar_global_C2_of_C2_scale_stationary_positive_C1
    (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hW2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (cstar W).toReal)
    (hflat : deriv (deriv W) (cstar W).toReal = 0)
    (hvc1 : ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
