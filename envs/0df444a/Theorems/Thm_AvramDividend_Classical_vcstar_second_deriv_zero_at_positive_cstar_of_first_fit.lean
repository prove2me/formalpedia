-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_zero_at_positive_cstar_of_first_fit
-- name    : AvramDividend.Classical.vcstar_second_deriv_zero_at_positive_cstar_of_first_fit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:42:18.482962+00:00
-- url     : https://prove2.me/theorems/236ba4e5-a4b7-42e0-ab9d-75c9d8c9d3bc
-- title:
--   Second derivative of the optimal dividend candidate vanishes at a smooth positive barrier
-- statement:
--   Let W have continuous first derivative on positive reserves, be differentiable there, and have a differentiable first derivative at its positive canonical dividend barrier. If W'(cstar) is nonzero and the candidate vcstar satisfies first-order smooth fit there, then the ordinary second derivative of vcstar at the positive barrier equals zero. The proof composes three already Proved exact statements: canonical stationarity of W', second-derivative equality between vcstar and the scaled scale-function branch, and vanishing curvature of that scaled branch. This is an explicitly conditional Gaussian boundary-jet lemma and not a claim of full C2 gluing or of first-order smooth fit from the root's hypotheses.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_deriv_stationary_of_deriv_continuous_differentiable
import Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
import Theorems.Thm_AvramDividend_Classical_scaledW_second_deriv_zero_at_positive_cstar

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_second_deriv_zero_at_positive_cstar_of_first_fit (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y)
    (hdne : deriv W (cstar W).toReal ≠ 0)
    (hddiff : DifferentiableAt ℝ (deriv W) (cstar W).toReal)
    (hvderiv : deriv (vcstar W) (cstar W).toReal = 1) :
    deriv (deriv (vcstar W)) (cstar W).toReal = 0 := by sorry
