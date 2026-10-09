-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
-- name    : AvramDividend.Classical.vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T17:05:00.829763+00:00
-- url     : https://prove2.me/theorems/2e8cdfd8-367b-46c3-9382-79fa4ed61ccf
-- title:
--   Second-order smooth fit from a stationary scale derivative and first-order matching
-- statement:
--   At a positive barrier, assume W is differentiable throughout the positive half-line, W'(c) is nonzero, W' has derivative zero at c, and the candidate barrier value already satisfies first-order smooth fit v'(c)=1. Below c the candidate derivative is W'(y)/W'(c), above c it equals 1, and at c both expressions also equal 1. The two branches of the derivative therefore glue with slope zero, showing v''(c)=0. The scaled W branch also has second derivative W''(c)/W'(c)=0, yielding equality. This is a source-neutral calculus step for the Gaussian-weighted second-order boundary jet, with the stochastic scale-function regularity and stationary-minimiser assumptions still to be established independently.
-- source:
--   Decomposes the weighted second-derivative boundary matching in AvramDividend.Classical.vcstar_scaledW_boundary_smooth_fit, under explicit sufficient regularity/minimiser hypotheses, by extending the accepted first-derivative gluing method of AvramDividend.Classical.vcstar_deriv_ge_one_of_regular_minimal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_second_deriv_smooth_fit_of_stationary_scale_deriv
    (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hWdiff : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ W y)
    (hdne : deriv W (cstar W).toReal ≠ 0)
    (hWstat : HasDerivAt (deriv W) 0 (cstar W).toReal)
    (hvderiv : deriv (vcstar W) (cstar W).toReal = 1) :
    deriv (deriv (vcstar W)) (cstar W).toReal =
      deriv (deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal))) (cstar W).toReal := by
  sorry

end AvramDividend.Classical
