-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
-- name    : AvramDividend.Classical.gaussian_esscher_canonical_volterra_identity_of_positive_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:15:24.683001+00:00
-- url     : https://prove2.me/theorems/945102b1-52e9-4cc5-821b-66b46f9f4a83
-- title:
--   Pointwise Gaussian Esscher Volterra identity for the canonical Lévy kernel
-- statement:
--   For the spectrally negative Lévy scale function W at q>0 with positive Gaussian coefficient σ, let φ>0 solve ψ(φ)=q and V(x)=exp(-φx)W(x) for x>0. Choose the canonical coefficient a=σ²/2, β equal to the Esscher-shifted drift appearing in gaussian_esscher_psi_volterra_denominator_of_root, and K the reflected-jump Gaussian double-tail kernel. Then for every x>0 the pointwise integrated Volterra equation aV(x)+∫₀ˣ(β+K(x-s))V(s)ds=x holds. This lemma isolates the analytic inversion and signed Laplace uniqueness step; integrability of K and positivity of a are handled independently by already-proved helpers. Its intended parent is gaussian_esscher_volterra_kernel_equation_of_positive_sigma (UUID 9d9714d3-ad96-479d-a82e-1561ae45c43e).
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Lévy process I, scale-function Laplace transform and Lévy–Khintchine exponent; Gaussian Esscher Volterra decomposition as formalised by the existing Prove2Me denominator and kernel lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem gaussian_esscher_canonical_volterra_identity_of_positive_sigma
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
    ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x := by sorry

end AvramDividend.Classical
