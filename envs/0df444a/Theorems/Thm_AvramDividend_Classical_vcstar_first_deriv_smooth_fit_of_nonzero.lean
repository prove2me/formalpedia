-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
-- name    : AvramDividend.Classical.vcstar_first_deriv_smooth_fit_of_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T17:00:40.314378+00:00
-- url     : https://prove2.me/theorems/ee1ed302-351c-459a-a6a9-fe127f14983e
-- title:
--   First-derivative smooth fit of the optimal barrier candidate from differentiability and a nonzero scale derivative
-- statement:
--   At a strictly positive optimal barrier c, assume W is differentiable at c and W'(c) is nonzero. The left scale-function branch W(x)/W'(c) and the right affine branch x-c+W(c)/W'(c) have matching value and derivative 1. Gluing their one-sided derivatives proves that v_cstar is differentiable at c and has the same derivative as the scaled W branch. This is a source-neutral first-order constituent of the boundary-jet smooth-fit theorem; the mission must separately establish the analytic hypotheses for the canonical scale function and the Gaussian second-order match.
-- source:
--   Direct boundary-gluing calculus based on the accepted source for AvramDividend.Classical.vcstar_deriv_ge_one_of_regular_minimal (submission a55320e0-a638-4347-8bcf-fbff7883672d) and definition (5.1) of Avram–Palmowski–Pistorius (2007). Relevant to vcstar_scaledW_boundary_smooth_fit and vcstar_scaledW_matched_weighted_jet_at_cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_first_deriv_smooth_fit_of_nonzero
    (W : ℝ → ℝ)
    (hc : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0) :
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal))
        (cstar W).toReal := by
  sorry

end AvramDividend.Classical
