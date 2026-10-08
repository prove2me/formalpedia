-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integrand_integrable
-- name    : AvramDividend.Classical.negative_jump_lk_integrand_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:19:26.97304+00:00
-- url     : https://prove2.me/theorems/6effeaf4-6258-4351-95ea-7dc97ede69c2
-- title:
--   Integrability of the spectrally negative Levy-Khintchine jump integrand
-- statement:
--   If a negative jump measure has finite square moment on (-1,0) and finite mass on jumps at most -1, then the canonical Levy-Khintchine compensated exponential jump integrand is integrable for every nonnegative Laplace parameter.
-- source:
--   Split the negative half-line into large and small jumps. Large jumps are bounded by one; small jumps are quadratically dominated by theta squared times y squared.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem negative_jump_lk_integrand_integrable
    (ν : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν) < ⊤)
    (hlarge : ν (Iic (-1 : ℝ)) < ⊤) :
    IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y)
      (Iio (0 : ℝ)) ν := by
  sorry

end AvramDividend.Classical
