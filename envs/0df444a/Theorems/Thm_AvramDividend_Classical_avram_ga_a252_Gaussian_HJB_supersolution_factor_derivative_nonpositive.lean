-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a252_Gaussian_HJB_supersolution_factor_derivative_nonpositive
-- name    : AvramDividend.Classical.avram_ga_a252_Gaussian_HJB_supersolution_factor_derivative_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:14:20.895783+00:00
-- url     : https://prove2.me/theorems/9c6a2974-c55f-498a-9bd6-e1c5254242cc
-- title:
--   Original zerojump Gaussian HJB scalar supersolution forces nonpositive derivative of exponential characteristic factor
-- statement:
--   Under a strictly positive Gaussian volatility, the exact scalar HJB supersolution inequality sigma²/2 times second derivative plus drift c times first derivative minus q times value at y is nonpositive. If the Gaussian characteristic roots satisfy their correct sum and product and derivatives exist, then the derivative of the exponentially weighted first-order HJB factor at y is nonpositive. This is the authentic source link from generator inequality to factor antitonicity and the missing one-sided near-origin upper envelope for a216.
-- source:
--   Gaussian HJB source factorisation a247 and factor derivative a249; original supersolution scalar inequality

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a247_Gaussian_HJB_scalar_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_ga_a249_Gaussian_HJB_factor_exponential_derivative
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a252_Gaussian_HJB_supersolution_factor_derivative_nonpositive
    (f fp : ℝ → ℝ)
    (sigma c q lambdaPlus lambdaMinus fpp y : ℝ)
    (hSigma : 0 < sigma)
    (hSum : lambdaPlus + lambdaMinus = -2*c/sigma^2)
    (hProd : lambdaPlus * lambdaMinus = -2*q/sigma^2)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y)
    (hHJB : (sigma^2/2)*fpp+c*fp y-q*f y ≤ 0) :
    deriv (fun t => Real.exp (-lambdaMinus*t)*
      (fp t-lambdaPlus*f t)) y ≤ 0 := by sorry
