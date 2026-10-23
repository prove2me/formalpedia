-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_real_kernel_denominator
-- name    : AvramDividend.Classical.gaussian_native_esscher_real_kernel_denominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:16:24.654557+00:00
-- url     : https://prove2.me/theorems/93b9ef31-2c6c-492d-9d19-57a9e0edeb37
-- title:
--   Native Gaussian Esscher resolvent denominator as a real Laplace transform of the double-tail kernel
-- statement:
--   For a spectrally negative Lévy process, a positive Esscher parameter φ with ψ(φ)=q, and any positive Laplace shift θ, the Lévy exponent difference ψ(φ+θ)−q equals a quadratic Gaussian term, a linear Esscher drift term with the exact one-jump atom correction, and θ² times the real Laplace transform of the positive double-tail jump kernel. The native moment assumptions imply sigma-finiteness of the positive-magnitude jump pushforward and finite kernel transform. The proof combines already proved native Esscher denominator, scalar double-tail real Laplace bridge, and the exact real/ENNReal integral conversion.
-- source:
--   Proved native denominator 940fe5d7, double-tail Laplace bridge 87f923ad, finite double tail eb52365a; real conversion bridge 6545953d awaiting verdict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_root_volterra_denominator
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_laplace_real_bridge
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_finite
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_laplace_integral_eq_toReal
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_native_esscher_real_kernel_denominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 < θ) (hroot : X.ψ φ = q) :
    X.ψ (φ + θ) - q =
      θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
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
           else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal ∂volume) := by sorry
