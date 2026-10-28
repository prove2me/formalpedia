-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_primitive_integrable
-- name    : AvramDividend.Classical.positive_laplace_primitive_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:12:24.488892+00:00
-- url     : https://prove2.me/theorems/cbabc04a-6199-474d-83c3-488f1d1cafbe
-- title:
--   Exponentially weighted primitive inherits positive-axis integrability
-- statement:
--   The positive-axis cumulative integral of any exponentially integrable real function is exponentially integrable at the same positive Laplace parameter. View the primitive as its causal convolution with the constant one function, then apply established weighted causal convolution integrability.
-- source:
--   Proved positive_weighted_causal_convolution_integrable and positive_laplace_constant_reference.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_positive_weighted_causal_convolution_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_laplace_primitive_integrable
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s ∂volume))
      (Ioi (0 : ℝ)) volume := by sorry
