-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_discount_bound_complete
-- name    : AvramDividend.Classical.levy_grid_upper_exit_discount_bound_complete
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:40:27.070953+00:00
-- url     : https://prove2.me/theorems/89845661-4ad7-43a0-a9c1-0381c46b25ba
-- title:
--   Unconditional integrable discounted upper-exit bound at a bounded two-sided Lévy grid stop
-- statement:
--   The actual spectrally negative Lévy process sampled at a capped strict two-sided grid exit has expected discounted upper-exit payoff bounded by exp(-θ upper) whenever θ≥0 and ψ(θ)≥0. Uses separately proved integrability and compensated exponential stopped moment upper bound; no extra stopped-payoff integrability assumption. This provides the finite-grid stochastic inequality needed before continuous-time first-passage limit.
-- source:
--   Composition of levy_grid_upper_exit_discount_integrable and levy_grid_upper_exit_exp_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_grid_upper_exit_discount_bound_complete
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 ≤ X.ψ θ)
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by sorry
