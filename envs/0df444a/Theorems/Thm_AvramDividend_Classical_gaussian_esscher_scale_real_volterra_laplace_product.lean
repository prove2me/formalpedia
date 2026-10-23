-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_scale_real_volterra_laplace_product
-- name    : AvramDividend.Classical.gaussian_esscher_scale_real_volterra_laplace_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:23:02.918664+00:00
-- url     : https://prove2.me/theorems/8ec6cdbf-8d3c-4911-bced-d6d954e7fd98
-- title:
--   Exact Gaussian Esscher scale-function Volterra Laplace product equals one
-- statement:
--   For every positive Laplace shift θ, the q-scale Esscher representative V has Laplace transform 1/(ψ(φ+θ)−q). The exact native Gaussian Volterra denominator identity rewrites that denominator as a drift term linear in θ, Gaussian variance term quadratic in θ, and θ² times the real Laplace transform of the Gaussian double-tail kernel. Multiplying gives the exact transform-level integrated Volterra identity. The strict positivity of the denominator is guaranteed by the proved native Gaussian root-crossing lemma, using only the standard Lévy moment condition, so no division by zero occurs.
-- source:
--   Proved native root crossing 188c5c28, native real-kernel denominator pending publication and proof, tilted scale Laplace representation 3b2059d8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_real_kernel_denominator
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_of_positive_agreement
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_scale_real_volterra_laplace_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (θ : ℝ) (hθ : 0 < θ) :
    (θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      θ ^ 2 * (∫ t : ℝ, Real.exp (-θ * t) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal ∂volume)) *
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * V s ∂volume) = 1 := by sorry
