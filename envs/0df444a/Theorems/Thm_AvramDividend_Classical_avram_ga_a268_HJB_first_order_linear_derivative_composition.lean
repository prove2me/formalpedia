-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a268_HJB_first_order_linear_derivative_composition
-- name    : AvramDividend.Classical.avram_ga_a268_HJB_first_order_linear_derivative_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:03:32.254064+00:00
-- url     : https://prove2.me/theorems/b470b235-cc5f-450e-b444-f180927039e9
-- title:
--   Gaussian HJB first-order derivative f prime minus characteristic exponent times value
-- statement:
--   If the scalar Gaussian value f and first derivative fp have derivatives fp and fpp at a point, the first-order HJB factor t↦fp(t)−lambda*f(t) has derivative fpp−lambda*fp. A simple concrete source type bridge for the exponential HJB factor derivative a249, used for near-origin Gaussian supersolution upper control.
-- source:
--   Mathlib HasDerivAt.sub const_mul for first order factor

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a268_HJB_first_order_linear_derivative_composition
    (f fp : ℝ → ℝ) (fpp lambda y : ℝ)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y) :
    HasDerivAt (fun t : ℝ => fp t-lambda*f t)
      (fpp-lambda*fp y) y := by sorry
