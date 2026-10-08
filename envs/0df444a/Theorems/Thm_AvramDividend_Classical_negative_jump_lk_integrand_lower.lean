-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integrand_lower
-- name    : AvramDividend.Classical.negative_jump_lk_integrand_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:25:59.343101+00:00
-- url     : https://prove2.me/theorems/64569834-299e-4ca3-af4e-120a6680cb7f
-- title:
--   Pointwise lower envelope for the spectrally negative Lévy–Khintchine jump integrand
-- statement:
--   For any real exponent parameter and any strictly negative jump y, the Levy–Khintchine compensated exponential integrand is nonnegative for -1<y<0 and bounded below by -1 on y≤-1. The unified indicator inequality is the pointwise input for a finite-large-jump-mass lower bound on the full exponent, needed in the Gaussian divergence branch.
-- source:
--   The scalar tangent inequality 1+z≤exp z and exp z>0, splitting the indicator at y=-1. The result does not claim the integral exists; integration requires separate Levy integrability assumptions.

import Mathlib
open MeasureTheory Set

namespace AvramDividend.Classical

theorem negative_jump_lk_integrand_lower
    (θ y : ℝ) (hy : y < 0) :
    -((Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y) ≤
      Real.exp (θ * y) - 1 -
        θ * y * ((Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y) := by
  sorry

end AvramDividend.Classical
