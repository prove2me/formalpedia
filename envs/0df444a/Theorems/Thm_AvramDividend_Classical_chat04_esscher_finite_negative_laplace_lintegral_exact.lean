-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_laplace_lintegral_exact
-- name    : AvramDividend.Classical.chat04_esscher_finite_negative_laplace_lintegral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:47:54.571865+00:00
-- url     : https://prove2.me/theorems/3dd97f5c-8ab5-41b7-9fbf-e7ac8d827894
-- title:
--   Exact nonnegative Lebesgue moment under the finite Esscher probability law
-- statement:
--   The nonnegative Lebesgue integral of exp(−εX_t) under the actual θ-Esscher finite-horizon measure is exactly exp(t[ψ(θ−ε)−ψ(θ)]) for θ≥ε≥0. This upgrades a real-valued expectation formula to the extended nonnegative integral used by Mathlib's sharp Markov probability inequality.
-- source:
--   By the independently proven tilted-law integrability of the negative exponential, use pinned `ofReal_integral_eq_lintegral_ofReal` and pointwise exp positivity, followed by the already proven exact real Esscher negative moment. This is a genuine finite moment, not an unverified Bochner integral value.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_negative_laplace_lintegral_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-ε * X.X t ω)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by sorry
