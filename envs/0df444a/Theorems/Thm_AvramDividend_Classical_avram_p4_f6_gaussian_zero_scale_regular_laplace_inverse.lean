-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:05:42.067975+00:00
-- url     : https://prove2.me/theorems/a8a2eaba-e9a3-44ec-a4b1-feee7fedeb3a
-- title:
--   Construct a continuous nonnegative zero-scale Laplace inverse for the original Gaussian Lévy exponent
-- statement:
--   Construct the zero-discount reciprocal-Laplace inverse for the original positive-Gaussian spectrally negative Lévy exponent. The proposed W₀ is supported on the nonnegative half-line, continuous and nonnegative there, and its Laplace transform is the exact reciprocal of ψ(θ). Monotonicity is deliberately excluded and treated by the independent analytic/probabilistic second child.
-- source:
--   Classical zero-scale construction from the potential measure/renewal function of the descending ladder-height process, based on Kuznetsov-Kyprianou-Rivero (2011). Separate analytic inverse transform existence, continuity and positivity from monotonicity. This is a proper strengthening over a bare Laplace inverse as it constructs a nonnegative continuous function.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_zero_scale_regular_laplace_inverse
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ W₀ : ℝ → ℝ,
      (∀ y < 0, W₀ y = 0) ∧
      (∀ y, 0 ≤ y → 0 ≤ W₀ y) ∧
      ContinuousOn W₀ (Ici 0) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) := by sorry
