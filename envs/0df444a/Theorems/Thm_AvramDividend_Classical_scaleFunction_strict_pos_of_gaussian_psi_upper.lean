-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian_psi_upper
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_gaussian_psi_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T11:39:50.56518+00:00
-- url     : https://prove2.me/theorems/da156aef-8586-48be-baf9-f5c4832558fb
-- title:
--   Strictly positive scale function in the Gaussian branch under explicit exponent bounds
-- statement:
--   For the Gaussian branch of the Avram spectrally negative Lévy model, the scale function is positive at every positive capital level assuming finite large-jump mass, integrability of the Lévy–Khintchine jump integrand, and a quadratic upper exponent bound. This conditionally assembles lower Gaussian divergence, the canonical scale-function Laplace identity, and the exponential-versus-quadratic positivity contradiction.
-- source:
--   Compose the process-specific Gaussian eventual exponent positivity theorem with the canonical strict-positivity bridge. Raise the cutoff to max(1,beta0) so that the assumed upper estimate X.psi(theta)≤C theta² applies. Since q>0 and C≥0, X.psi(theta)-q≤C(1+theta²). Source-faithful assumptions; no retired exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_strict_pos_of_gaussian_psi_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hν : X.ν (Iic (-1 : ℝ)) ≠ ⊤)
    (hjump : ∀ θ : ℝ, 0 ≤ θ →
      IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y * ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) (Iio (0 : ℝ)) X.ν)
    (C : ℝ) (hC : 0 ≤ C)
    (hupper : ∀ θ : ℝ, 1 ≤ θ → X.ψ θ ≤ C * θ ^ 2) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  sorry

end AvramDividend.Classical
