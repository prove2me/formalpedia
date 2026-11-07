-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_potential_measure_exists
-- name    : AvramDividend.Classical.avram_p4_f6_gaussian_zero_potential_measure_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T10:11:11.791327+00:00
-- url     : https://prove2.me/theorems/2ca4039e-2b9e-4787-ae81-a37747b53f4d
-- title:
--   Positive original Gaussian zero-scale potential measure with reciprocal-exponent Laplace transform
-- statement:
--   Construct the killed/ladder-height zero potential measure supported on strictly positive reserves with exact Laplace transform 1/ψ(θ) for θ≥0, ψ(θ)>0. Gaussian positivity and Standing ensure a positive locally finite resolvent measure. This measure-valued stage is independent from the regularity and density of its absolutely continuous representative.
-- source:
--   Wiener-Hopf factorisation and the renewal/potential measure of the spectrally negative Lévy ladder process. The Laplace transform formula is classical (Kyprianou, Kuznetsov, Rivero 2011, Theory of Scale Functions). This is a genuine measure-valued construction stage toward public child a8a2eaba.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_gaussian_zero_potential_measure_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : 0 < X.σ) :
    ∃ μ : Measure ℝ,
      μ (Iic (0 : ℝ)) = 0 ∧
      (∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) μ ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂μ = (X.ψ θ)⁻¹) := by sorry
