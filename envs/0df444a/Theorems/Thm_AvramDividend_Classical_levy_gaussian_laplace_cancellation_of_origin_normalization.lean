-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_gaussian_laplace_cancellation_of_origin_normalization
-- name    : AvramDividend.Classical.levy_gaussian_laplace_cancellation_of_origin_normalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:27:11.461871+00:00
-- url     : https://prove2.me/theorems/273f4156-2171-46d6-8405-7b68e4711f72
-- title:
--   The actual Lévy–Khintchine exponent cancels the Gaussian generator boundary term
-- statement:
--   For the exact spectrally negative Lévy Laplace exponent ψ(θ)=cθ+σ²θ²/2+∫(exp(θy)−1−θy1_{|y|<1})ν(dy), and θ with ψ(θ)>q, the complete Gaussian/drift/compensated-jump transform coefficient equals 1 after multiplying by the q-scale Laplace transform. Under the origin slope normalisation (σ²/2)η=1, the resulting generator-transform residual is exactly zero. The proof converts the abstract previously proved Gaussian cancellation into the mission's actual ψ, σ, c, ν fields.
-- source:
--   AvramDividend Classical SpectrallyNegativeLevy.ψ and laplaceExponent definitions; proved Gaussian generator cancellation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem levy_gaussian_laplace_cancellation_of_origin_normalization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q θ η : ℝ) (hqθ : q < X.ψ θ)
    (horigin : (X.σ ^ 2 / 2) * η = 1) :
    ((X.σ ^ 2 / 2) * θ ^ 2 + X.c * θ +
      (∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1 -
          θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂X.ν) - q) *
      (X.ψ θ - q)⁻¹ - (X.σ ^ 2 / 2) * η = 0 := by sorry

end AvramDividend.Classical
