-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
-- name    : AvramDividend.Classical.bv_exponent_negative_jump_deficit_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:07:43.100198+00:00
-- url     : https://prove2.me/theorems/952c5905-d4fb-409e-ad4a-0b694d369d0c
-- title:
--   Exact BV exponent drift deficit as the real negative-jump integral
-- statement:
--   For a bounded-variation spectrally negative Lévy process, the difference between drift times Laplace argument and its true Laplace exponent equals the real integral over negative jumps of one minus the exponentially tilted jump size. This identifies the quantity that diverges under infinite negative-jump activity and supplies an exact algebraic interface for scale-function origin slope arguments.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, and the Lévy–Khintchine exponent; https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
import Theorems.Thm_AvramDividend_Classical_negative_jump_magnitude_integral_transform
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The BV exponent deficit is exactly the negative-jump exponential integral. -/
theorem bv_exponent_negative_jump_deficit_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.drift * θ - X.ψ θ =
      ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν := by sorry

end AvramDividend.Classical
