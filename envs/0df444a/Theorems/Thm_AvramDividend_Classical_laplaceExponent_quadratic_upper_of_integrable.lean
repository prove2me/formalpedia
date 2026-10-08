-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplaceExponent_quadratic_upper_of_integrable
-- name    : AvramDividend.Classical.laplaceExponent_quadratic_upper_of_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T00:25:56.492387+00:00
-- url     : https://prove2.me/theorems/5f73cc0c-258b-4802-ba65-8905fdf6db6f
-- title:
--   Quadratic upper bound for a spectrally negative Levy exponent
-- statement:
--   For theta at least one, the canonical spectrally negative Levy exponent is bounded above by an explicit constant times theta squared, provided the jump integrand and small-jump square moment are integrable.
-- source:
--   Drift is bounded by |c| theta squared, the Gaussian term is already quadratic, and the jump term is controlled by the negative-jump quadratic integral bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem laplaceExponent_quadratic_upper_of_integrable
    (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) (hθ : 1 ≤ θ)
    (hint : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν)
    (hy2 : IntegrableOn (fun y : ℝ => y ^ 2) (Ioo (-1 : ℝ) 0) ν) :
    laplaceExponent c σ ν θ ≤
      (|c| + σ ^ 2 / 2 +
        ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂ν) * θ ^ 2 := by
  sorry

end AvramDividend.Classical
