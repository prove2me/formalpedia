-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_residual_continuous_on_positive
-- name    : AvramDividend.Classical.gaussian_esscher_volterra_residual_continuous_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:07:58.179994+00:00
-- url     : https://prove2.me/theorems/5739e358-a6c7-4f62-b5b9-086822d1eba5
-- title:
--   Continuity of the canonical Gaussian Esscher Volterra residual
-- statement:
--   For the Gaussian Esscher tilted scale V and canonical coefficients a, β and integrable double-tail kernel K, the residual F(x)=aV(x)+∫_0^x(β+K(x-s))V(s)ds is continuous for x>0. This isolates the analytic convolution regularity step needed to upgrade signed Laplace uniqueness from almost everywhere to pointwise equality. Parent: gaussian_esscher_canonical_volterra_identity_of_positive_sigma.
-- source:
--   Gaussian Esscher Volterra proof programme, based on the scale-function transform and Lévy–Khintchine denominator in Avram, Palmowski and Pistorius (2007), together with the pinned Prove2Me convolution and Laplace-uniqueness lemmas.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem gaussian_esscher_volterra_residual_continuous_on_positive
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
    ContinuousOn (fun x : ℝ =>
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume)) (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
