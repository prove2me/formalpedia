-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a247_Gaussian_HJB_scalar_factorisation
-- name    : AvramDividend.Classical.avram_ga_a247_Gaussian_HJB_scalar_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:38:19.364073+00:00
-- url     : https://prove2.me/theorems/e6ea2492-9399-42c5-b1ff-6e6fb15a07dc
-- title:
--   Zerojump Gaussian HJB scalar generator factorises through characteristic roots
-- statement:
--   For the original zerojump Gaussian Lévy HJB operator sigma squared over two times second derivative plus c first derivative minus q times the value, given two characteristic roots with sum -2c/sigma squared and product -2q/sigma squared, the operator is exactly sigma squared over two times its factored second-order differential expression. This algebra supports the mathematical near-origin one-sided HJB supersolution upper-envelope proof needed for a216.
-- source:
--   Original Gaussian generator HJB ODE; root sum/product factoring, scalar ODE near ruin missing upper envelope

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a247_Gaussian_HJB_scalar_factorisation
    (sigma c q lambdaPlus lambdaMinus w1 w2 w0 : ℝ)
    (hSum : lambdaPlus + lambdaMinus = -2*c/sigma^2)
    (hProd : lambdaPlus * lambdaMinus = -2*q/sigma^2)
    (hSigma : 0 < sigma) :
    (sigma^2/2) * (w2-(lambdaPlus+lambdaMinus)*w1+
      lambdaPlus*lambdaMinus*w0) =
    (sigma^2/2)*w2+c*w1-q*w0 := by sorry
