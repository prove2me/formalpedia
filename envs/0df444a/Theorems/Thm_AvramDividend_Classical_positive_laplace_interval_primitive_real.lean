-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
-- name    : AvramDividend.Classical.positive_laplace_interval_primitive_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:23:36.496994+00:00
-- url     : https://prove2.me/theorems/9f40ea02-9c61-4aad-8f22-f3c265f85312
-- title:
--   Laplace transform and integrability of real interval primitives
-- statement:
--   For an exponentially integrable real function on positive reserves, its interval integral from zero to reserve is exponentially integrable and has Laplace transform divided by the positive transform parameter. Connect the interval integral and Ioc cumulative-integral conventions almost everywhere on x>0, then invoke the established two cumulative Laplace theorems.
-- source:
--   Proved positive_laplace_primitive_integrable and positive_laplace_cumulative_real, intervalIntegral.integral_of_le.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_positive_laplace_cumulative_real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.positive_laplace_interval_primitive_real
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in (0 : ℝ)..x, f s)) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ s in (0 : ℝ)..x, f s)) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * f s) / θ := by sorry
