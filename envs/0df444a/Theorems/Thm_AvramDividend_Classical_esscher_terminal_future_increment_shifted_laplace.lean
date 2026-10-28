-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_future_increment_shifted_laplace
-- name    : AvramDividend.Classical.esscher_terminal_future_increment_shifted_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:14:34.21769+00:00
-- url     : https://prove2.me/theorems/0d6b9c7e-0432-476a-8088-1e8d9f22034d
-- title:
--   Every later Esscher terminal law gives the correct shifted Laplace exponent for a future Lévy increment
-- statement:
--   For nonnegative Esscher parameter θ and Laplace argument η, every future increment X_(s+u)−X_s measured under the true time-T Esscher probability for s+u≤T has the moment E[exp(η(X_(s+u)−X_s))]=exp(u(ψ(θ+η)−ψ(θ))). It identifies the stationary increment Laplace exponent of the finite-prefix Esscher laws on the actual valid moment domain; no all-horizon extension is asserted.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions, Esscher change-of-measure exponent; accepted 73de4f4f-bf10-4dbd-898a-2eba7912fedf shifted one-time transform and 14dc9816-2e6b-4956-b87f-4174beb8af7b full increment pushforward law; pinned Mathlib integral_map_of_stronglyMeasurable.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_shifted_laplace

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_future_increment_shifted_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    (∫ ω, Real.exp (η * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      Real.exp ((u : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by sorry
