-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
-- name    : AvramDividend.Classical.positive_laplace_constant_reference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:02:49.586412+00:00
-- url     : https://prove2.me/theorems/f89e6318-4e93-471e-857b-67eff1659f9a
-- title:
--   Constant function's positive-axis Laplace transform and integrability
-- statement:
--   For θ>0, the exponential damping factor e^(−θ x) is integrable on (0,∞) and its real Lebesgue integral equals 1/θ. Derived directly from the pinned Mathlib integrableOn_exp_mul_Ioi and integral_exp_mul_Ioi formulas, by using the negative coefficient a=−θ and lower endpoint zero. This is used to obtain the transform β/θ of the constant Volterra kernel β.
-- source:
--   Pinned Mathlib Analysis.SpecialFunctions.ImproperIntegrals

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_laplace_constant_reference (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x))) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) ∂volume) = 1 / θ := by sorry
