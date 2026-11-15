-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
-- name    : AvramDividend.Classical.avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:45:33.513587+00:00
-- url     : https://prove2.me/theorems/959fa72c-0994-43e2-9502-f175e556eb4b
-- title:
--   Derivative of the exponentially rescaled value source near zero.
-- statement:
--   Derivative of the exponentially rescaled value source near zero. Source step in the original Gaussian HJB near-zero one-sided upper control, used with a249/a250/a251.
-- source:
--   Source-exact zero-jump Gaussian HJB origin weighted derivative comparison

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
    (f fp : ℝ → ℝ) (alpha y : ℝ)
    (hf : HasDerivAt f (fp y) y) :
    HasDerivAt (fun t => Real.exp (-alpha*t)*f t)
      (Real.exp (-alpha*y)*(fp y-alpha*f y)) y := by sorry
