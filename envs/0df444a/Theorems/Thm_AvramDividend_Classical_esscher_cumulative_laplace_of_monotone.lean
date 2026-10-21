-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_cumulative_laplace_of_monotone
-- name    : AvramDividend.Classical.esscher_cumulative_laplace_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:33:04.984624+00:00
-- url     : https://prove2.me/theorems/ffbb7361-9e11-4182-b5a8-eabef0f6738b
-- title:
--   Laplace cumulative representation of a q-scale Esscher factor under supplied positive tilt
-- statement:
--   Under a supplied positive Esscher tilt, monotonicity of its scale factor and an explicit eventual Laplace domain, construct a positive cumulative measure representing the damped scale function and show both Laplace kernels are integrable with equal integrals for all parameters above one cutoff. This isolates analytic measure construction and exponential-shift calculations from the remaining first-passage stochastic argument.
-- source:
--   The canonical IsScaleFunction q-Laplace transform, pinned Stieltjes cumulative measure theorem and Real.exp_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_cumulative_laplace_of_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (φ : ℝ) (hφ : 0 < φ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ)) :
    ∃ (β : Measure ℝ) (φ' b : ℝ),
      0 < φ' ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ' * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ' * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by sorry
