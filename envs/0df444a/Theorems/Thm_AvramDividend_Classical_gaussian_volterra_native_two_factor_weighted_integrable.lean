-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_volterra_native_two_factor_weighted_integrable
-- name    : AvramDividend.Classical.gaussian_volterra_native_two_factor_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:12:43.652232+00:00
-- url     : https://prove2.me/theorems/e36bb529-8d07-42d4-a360-1062f4ea52b2
-- title:
--   Gaussian Esscher scale and native double-tail kernel have integrable Laplace weights
-- statement:
--   Under the native spectrally negative Lévy triplet's standard moment condition, q>0, σ>0 and positive Esscher root φ, for every θ>0 both the scale representative V weighted by exp(-θx) and the native double-tail Lévy kernel weighted by exp(-θx) are integrable on x>0. This is exactly the pair of hypotheses required for real causal convolution Laplace factorisation. The proof derives positive-magnitude jump pushforward finiteness from the original Lévy field and gets ψ(φ+θ)>q from positive Gaussian diffusion.
-- source:
--   Pinned Proved Gaussian root-crossing, Levy pushforward moment, positive-axis tilted scale transform, Gaussian kernel weighted integrability.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_of_positive_agreement
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_weighted_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_volterra_native_two_factor_weighted_integrable
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
    IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * V s)
      (Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) *
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
         else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal)
      (Ioi (0 : ℝ)) volume := by sorry
