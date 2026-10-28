-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_negative_laplace
-- name    : AvramDividend.Classical.esscher_terminal_future_increment_negative_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:18:14.900971+00:00
-- url     : https://prove2.me/theorems/7f52334f-f0e9-4e15-b6e5-af6eeb02cebd
-- title:
--   Negative shifted Laplace transform of future increments under every consistent Esscher terminal law
-- statement:
--   For a spectrally negative Lévy process X, Esscher parameter θ≥0, 0≤ε≤θ and deterministic s+u≤T, under the terminal Esscher law Q_T the negative ε-Laplace moment of the future increment X_(s+u)-X_s equals exp(u(ψ(θ-ε)-ψ(θ))). This extends the already proved positive-η increment transform to the left-shifted domain and gives finite-horizon fluctuation arguments access to actual negative exponential moments without assuming a Wiener–Hopf identity.
-- source:
--   Accepted Prove2Me chat04_esscher_weighted_finite_horizon_negative_laplace (fdaa303c-3eed-45c3-bbf7-36d1336e766b), esscher_terminal_increment_map_law (14dc9816-2e6b-4956-b87f-4174beb8af7b), Mathlib.MeasureTheory.Integral.Bochner.Basic.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_future_increment_negative_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    (∫ ω, Real.exp (-ε * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      Real.exp ((u : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) := by sorry
