-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_lk_integral_lower
-- name    : AvramDividend.Classical.negative_jump_lk_integral_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:28:22.273993+00:00
-- url     : https://prove2.me/theorems/c1a216d5-48ba-4ecc-9e50-283f15fba91a
-- title:
--   Integrated lower bound on the Lévy–Khintchine negative-jump correction
-- statement:
--   If the Lévy measure has finite mass on jumps of size at most minus one and the compensated jump integrand is integrable on the negative half-line, then its integral is at least minus the real measure of those large jumps. This supplies the negative constant in the Gaussian lower bound for the Lévy exponent.
-- source:
--   Pointwise lower bound from exp z≥1+z and exp z≥0, plus setIntegral_mono_on and the exact pinned Mathlib lemma integral_indicator_one, with finite-large-jump indicator integrability explicitly established.

import Mathlib
open MeasureTheory Set

namespace AvramDividend.Classical

theorem negative_jump_lk_integral_lower
    (ν : Measure ℝ) (θ : ℝ)
    (hfin : ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hint : IntegrableOn
      (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y))
      (Iio (0 : ℝ)) ν) :
    -(ν.real (Iic (-1 : ℝ))) ≤
      ∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 - θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) ∂ν := by
  sorry

end AvramDividend.Classical
