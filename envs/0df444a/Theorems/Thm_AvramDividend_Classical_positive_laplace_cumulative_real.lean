-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_laplace_cumulative_real
-- name    : AvramDividend.Classical.positive_laplace_cumulative_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:11:00.604238+00:00
-- url     : https://prove2.me/theorems/256a45cd-4ee9-460d-a375-c81497619f7d
-- title:
--   Laplace transform of the positive-axis cumulative integral of a real function
-- statement:
--   If e^(-θx) f(x) is integrable on x>0 with θ>0, the real Laplace transform of x↦∫_(0,x] f(s) ds is exactly (1/θ) times the transform of f. This uses the proved positive-half-line causal convolution transform with right factor 1, whose Laplace transform is 1/θ. The required endpoint convention is the closed-right interval Ioc 0 x, as in the Gaussian Volterra equation.
-- source:
--   Proved positive_real_laplace_causal_convolution and pending positive_laplace_constant_reference

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_real_laplace_causal_convolution
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_laplace_cumulative_real
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s ∂volume) ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * f s ∂volume) / θ := by sorry
