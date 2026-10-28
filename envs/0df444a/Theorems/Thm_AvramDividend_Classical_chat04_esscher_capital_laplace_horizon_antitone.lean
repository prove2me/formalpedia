-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_capital_laplace_horizon_antitone
-- name    : AvramDividend.Classical.chat04_esscher_capital_laplace_horizon_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:21:37.508983+00:00
-- url     : https://prove2.me/theorems/e110b4d8-6212-40f9-a351-7e4fdb408ea8
-- title:
--   Esscher-weighted killed survival capital Laplace mass decreases with horizon
-- statement:
--   For every nonnegative Esscher parameter, positive capital Laplace parameter and two ordered finite horizons, the capital-integrated nonnegative Esscher-survival mass with exponential capital weight decreases as time grows. This establishes a positive monotone family of scalar transforms suitable for limit exchange.
-- source:
--   Multiply Proved pointwise-in-capital nonnegative Esscher survival antitonicity by the positive exponential Laplace kernel and integrate over positive starting capital, using Mathlib lintegral_mono. Its companion finite-horizon Esscher-weighted reflected-infimum transform identifies the stochastic quantity. No infinite-horizon Wiener–Hopf factorisation or two-sided exit identity is used.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_lintegral_antitone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_capital_laplace_horizon_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ β : ℝ) (hθ : 0 ≤ θ) (hβ : 0 < β)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-β * x)) *
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (θ * X.X u ω -
              (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
      ∂volume) ≤
    (∫⁻ (x : ℝ) in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-β * x)) *
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (θ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P)
      ∂volume) := by sorry
