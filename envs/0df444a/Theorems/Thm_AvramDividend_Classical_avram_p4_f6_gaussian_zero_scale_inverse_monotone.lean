-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_scale_inverse_monotone
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_inverse_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:05:36.643536+00:00
-- url     : https://prove2.me/theorems/68454ad6-49a2-4e61-a57b-614650b82ae2
-- title:
--   Monotonicity of the original Gaussian continuous nonnegative zero-scale reciprocal Laplace inverse
-- statement:
--   For the original Gaussian spectrally negative Lévy exponent, any nonnegative continuous zero-resolvent density supported on nonnegative capital with reciprocal-exponent Laplace transform is monotone. This is independent of construction of the density and requires fluctuation/renewal structure plus uniqueness of Laplace transforms.
-- source:
--   Classical monotonicity property of the scale function, derived from two-sided exit potential and uniqueness of Laplace transforms, Kuznetsov-Kyprianou-Rivero (2011). A separate genuinely mathematical obligation from existence of a regular reciprocal-Laplace density.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_inverse_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (W₀ : ℝ → ℝ)
    (hSupp : ∀ y < 0, W₀ y = 0)
    (hNonneg : ∀ y, 0 ≤ y → 0 ≤ W₀ y)
    (hCont : ContinuousOn W₀ (Ici 0))
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) :
    MonotoneOn W₀ (Ici 0) := by sorry
