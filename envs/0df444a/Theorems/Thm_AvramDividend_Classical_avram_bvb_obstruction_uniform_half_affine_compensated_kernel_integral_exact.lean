-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:46:23.124573+00:00
-- url     : https://prove2.me/theorems/f98142c5-bdd2-44f7-ba4f-1f079cf17768
-- title:
--   Exact compensated negative-uniform Poisson affine kernel integral at a positive reserve
-- statement:
--   For y>0, integrate the compensated affine candidate jump kernel on the unit negative Lévy mark interval (−1,0). The kernel vanishes above reserve y≥1 and integrates to y(y−1)/2 for 0<y<1. This is the missing analytic generator equality for the positive-cap BV drift-only cash counterexample.
-- source:
--   For 0<y<1, the integrand is −(y+1/2+z) on (−1,−y) and zero on [−y,0), giving y(y−1)/2 by the fundamental theorem of calculus; for y≥1 it is identically zero on (−1,0). Endpoints have zero Lebesgue measure. Independently verified symbolically with SymPy.

import Mathlib
open MeasureTheory Set Real

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_half_affine_compensated_kernel_integral_exact (y : ℝ) (hy : 0 < y) :
    (∫ z in Ioo (-1 : ℝ) 0,
      (if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0)
        ∂(volume : Measure ℝ)) =
    if y < 1 then y * (y - 1) / 2 else 0 := by sorry
