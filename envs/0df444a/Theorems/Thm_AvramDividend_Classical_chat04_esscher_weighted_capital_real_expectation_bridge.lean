-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_real_expectation_bridge
-- name    : AvramDividend.Classical.chat04_esscher_weighted_capital_real_expectation_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:19:41.007563+00:00
-- url     : https://prove2.me/theorems/3c50d08b-2ae7-49e9-9f8e-79d0cb9c67e9
-- title:
--   Real expectation form of the Esscher-weighted killed survival Laplace transform
-- statement:
--   For a nonnegative Esscher parameter and positive capital Laplace parameter, the actual killed Esscher capital transform equals the ENNReal embedding of a finite ordinary real expectation of the reflected running-infimum exponential times the compensated Esscher exponential.
-- source:
--   The Proved exact finite-horizon weighted ENNReal transform identifies the pathwise factors. The Proved weighted reflected-infimum integrability and positivity supply ofReal_integral_eq_lintegral_ofReal. This converts the killed-semigroup capital transform into the ordinary Wiener-Hopf weighted expectation, without assuming the infinite-time Wiener-Hopf identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_reflected_infimum_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_capital_real_expectation_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (∫ ω : Ω,
      (Real.exp (-β * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / β) *
      Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by sorry
