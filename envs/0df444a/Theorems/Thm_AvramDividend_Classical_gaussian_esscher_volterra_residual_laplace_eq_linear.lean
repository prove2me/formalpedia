-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_residual_laplace_eq_linear
-- name    : AvramDividend.Classical.gaussian_esscher_volterra_residual_laplace_eq_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:07:53.735511+00:00
-- url     : https://prove2.me/theorems/af9be5d4-f4d5-4532-9475-cb91e4d46bba
-- title:
--   Laplace transform of the Gaussian Esscher Volterra residual equals that of x
-- statement:
--   For the same Gaussian Esscher canonical residual F, for every θ>0 its exponentially damped restriction to x>0 is integrable, and its Laplace integral is 1/θ². Use the proved Gaussian scale Volterra Laplace product identity, L1 double-tail kernel, causal convolution product formula and strict-root transform bounds. Parent: gaussian_esscher_canonical_volterra_identity_of_positive_sigma.
-- source:
--   Gaussian Esscher Volterra proof programme, based on the scale-function transform and Lévy–Khintchine denominator in Avram, Palmowski and Pistorius (2007), together with the pinned Prove2Me convolution and Laplace-uniqueness lemmas.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem gaussian_esscher_volterra_residual_laplace_eq_linear
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K : ℝ → ℝ)
    (ha : a = X.σ ^ 2 / 2)
    (hβ : β =
      X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y))))
    (hK : K = fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal) :
    ∀ θ : ℝ, 0 < θ →
      IntegrableOn (fun x : ℝ =>
        Real.exp (-(θ * x)) *
          (a * V x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * V s ∂volume)))
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) *
          (a * V x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * V s ∂volume)) ∂volume) =
        (1 / θ) ^ 2 := by sorry

end AvramDividend.Classical
