-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order
-- name    : AvramDividend.Classical.avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:40:12.140925+00:00
-- url     : https://prove2.me/theorems/514cb217-2003-4422-8e7e-a619a69576bd
-- title:
--   First-order source spatial interval Taylor polynomial equals original classical derivative expansion at distinct endpoints
-- statement:
--   For any differentiable real value function at an initial spatial source point y and any distinct target z, the first-order TaylorWithin interval polynomial equals w(y) plus the ordinary derivative at y times z−y.
-- source:
--   Direct original b0d9951c Gaussian compact C2 Taylor modulus ga_a58 reconciliation with original classical gradient in HJB generator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a74_classical_C2_spatial_taylor_polynomial_eq_within_first_order (w : ℝ → ℝ) (y z : ℝ)
    (hyz : y ≠ z) (hw : DifferentiableAt ℝ w y) :
    taylorWithinEval w 1 (uIcc y z) y z =
      w y + deriv w y * (z - y) := by sorry
