-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_jump_magnitude_truncated_moment_finite
-- name    : AvramDividend.Classical.positive_jump_magnitude_truncated_moment_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T00:20:17.81405+00:00
-- url     : https://prove2.me/theorems/9a431fac-f00f-4efa-bf08-601d1510d126
-- title:
--   Finite positive-jump magnitude truncation moment from BV Lévy hypotheses
-- statement:
--   For any Lévy jump measure on the real line with a finite small-negative-jump first moment on (-1,0) and a finite Lévy quadratic truncation moment over the whole line, the pushforward to nonnegative jump magnitudes z=max(-y,0) has a finite truncated first moment ∫ min(z,1) μ(dz). This is the exact bridge between the canonical SpectrallyNegativeLevy.BoundedVariation and ν_integrable fields and the discounted-jump dominated-convergence theorem used to construct the positive renewal resolvent.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Lebesgue.Map lintegral_map, lintegral_mono, lintegral_indicator, and ENNReal.add_lt_top; canonical AvramDividend_Classical_SpectrallyNegativeLevy bounded variation and ν_integrable hypotheses

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Bounded-variation small jumps and the Lévy quadratic condition imply
a finite truncated first moment for positive jump magnitudes. -/
theorem positive_jump_magnitude_truncated_moment_finite (ν : Measure ℝ)
    (hsmall : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) ≠ ⊤)
    (hquad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) ≠ ⊤) :
    (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1) ∂
      Measure.map (fun y : ℝ => Real.toNNReal (-y)) ν) ≠ ⊤ := by
  sorry

end AvramDividend.Classical
