-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_laplace_exponent_tail
-- name    : AvramDividend.Classical.original_purejump_laplace_exponent_tail
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:51:43.053326+00:00
-- url     : https://prove2.me/theorems/0fded7ba-04d9-4ecf-8fe6-044f9c8c72cb
-- title:
--   Exact original pure-jump Lévy exponent-to-negative-tail formula
-- statement:
--   For the actual original spectrally negative Lévy process in Standing with σ=0, the compensated LK exponent divided by θ is exactly original drift c plus the integral of original large signed marks y≤-1 plus the real Lebesgue integral over t>0 of (1-exp(-θt))*ν((-∞,-t)). The theorem asserts integrability of that original physical tail kernel. It is source-faithful under infinite small-jump variation and finite Standing large-mark first moment, preserving the actual negative jump measure and compensation cutoff.
-- source:
--   Pinned exact laplaceExponent definition; Avram–Palmowski–Pistorius (2007), spectrally negative Lévy exponent and descending ladder-height tail transform. Proved children: 0e758fb9 signed large-mark integrability, new original_negative_levy_tail_tonelli and compensated_jump_exponential_primitive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.original_purejump_laplace_exponent_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-θ * t)) * (X.ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    X.ψ θ / θ =
      X.c + (∫ y in Iic (-1 : ℝ), y ∂X.ν) +
      (∫ t in Ioi (0 : ℝ),
        (1 - Real.exp (-θ * t)) * (X.ν (Iio (-t))).toReal) := by sorry
