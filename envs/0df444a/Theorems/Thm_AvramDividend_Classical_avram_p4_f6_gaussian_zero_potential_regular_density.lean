-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_potential_regular_density
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_zero_potential_regular_density
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:11:11.456212+00:00
-- url     : https://prove2.me/theorems/10b44554-b6c2-4b7a-b895-f31a524d23fd
-- title:
--   Gaussian zero-scale potential measure has a continuous nonnegative reciprocal Laplace density
-- statement:
--   For a positive supported potential measure with reciprocal original Lévy exponent transform, obtain a continuous nonnegative density W₀ with the same Laplace family. The Gaussian coefficient smooths the potential measure, and uniqueness of Laplace transforms identifies its density. Monotonicity is treated separately by the existing zero-scale inverse-monotonicity child.
-- source:
--   Gaussian smoothing of spectrally-negative Lévy potential measures and uniqueness of Laplace transforms; classical q-scale existence theory, Kyprianou, Kuznetsov, Rivero (2011). Source-faithful density-regularity condition for child a8a2eaba.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_zero_potential_regular_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ)
    (μ : Measure ℝ)
    (hSupport : μ (Iic (0 : ℝ)) = 0)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) μ ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂μ = (X.ψ θ)⁻¹) :
    ∃ W₀ : ℝ → ℝ,
      (∀ y < 0, W₀ y = 0) ∧
      (∀ y, 0 ≤ y → 0 ≤ W₀ y) ∧
      ContinuousOn W₀ (Ici 0) ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W₀ y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W₀ y = (X.ψ θ)⁻¹) := by sorry
