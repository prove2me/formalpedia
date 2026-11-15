-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
-- name    : AvramDividend.Classical.avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:39:33.049451+00:00
-- url     : https://prove2.me/theorems/9fc36032-8b5c-43da-9337-e4fb252a3211
-- title:
--   Gaussian scalar HJB exponential weighted first-order factor has derivative equal to factored ODE
-- statement:
--   Given first and second real derivatives of a scalar Gaussian HJB candidate f, differentiate exp(-lambdaMinus t) times (f prime minus lambdaPlus f) exactly. The derivative equals the positive exponential factor times the second-order factored HJB differential expression. With root sum/product and Gaussian generator inequality this is nonpositive, the first analytic step in proving a global one-sided upper bound for the candidate function near zero, a missing component of a216.
-- source:
--   Scalar Gaussian HJB operator on (0,a], product, chain, exponential derivative; a247/a248 near-origin proof route

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
    (f fp : ℝ → ℝ) (fpp lambdaPlus lambdaMinus y : ℝ)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y) :
    HasDerivAt (fun t => Real.exp (-lambdaMinus*t) *
      (fp t-lambdaPlus*f t))
      (Real.exp (-lambdaMinus*y) *
        (fpp-(lambdaPlus+lambdaMinus)*fp y+
          lambdaPlus*lambdaMinus*f y)) y := by sorry
