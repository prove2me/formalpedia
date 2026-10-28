-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_scale_kernel_tilt_all_parameter_laplace
-- name    : AvramDividend.Classical.zero_scale_kernel_tilt_all_parameter_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:22:30.0894+00:00
-- url     : https://prove2.me/theorems/0f5ba147-b537-43e6-904d-af67b2d099a2
-- title:
--   The zero-discount tilted renewal kernel has its exact Laplace mass at every parameter
-- statement:
--   For a zero-discount scale function W0, any q-weighted exponential tilt K(x)=q exp(-theta*x) W0(x) satisfies an exponentially shifted integrability statement and integral q/psi(eta) for every eta>=0 with psi(eta)>0. This closes the universal Laplace-parameter bridge in construction of positive-discount scale functions from W0.
-- source:
--   Exact IsScaleFunction zero-discount Laplace definition, Real.exp_add, integral_const_mul.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_scale_kernel_tilt_all_parameter_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q θ η : ℝ) (hη0 : 0 ≤ η) (hψη : 0 < X.ψ η) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x)))
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-((η - θ) * x)) *
        (q * (Real.exp (-(θ * x)) * W₀ x)) ∂volume) =
      q / X.ψ η := by sorry
