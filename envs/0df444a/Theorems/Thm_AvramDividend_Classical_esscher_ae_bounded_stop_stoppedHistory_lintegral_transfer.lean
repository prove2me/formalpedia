-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_lintegral_transfer
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_lintegral_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:50:38.875315+00:00
-- url     : https://prove2.me/theorems/b51dbc40-c72d-499e-8201-b61ad93a917f
-- title:
--   Arbitrary nonnegative stopped-history reward transfer at an almost-surely bounded Esscher stop
-- statement:
--   For any genuinely stopped-history-measurable observable Y at an almost-surely bounded stopping time tau and any measurable nonnegative reward g, the full Lebesgue integral of g(Y) under the finite-terminal Esscher law Q_T equals its integral under the realised stopped-time Esscher likelihood Q_tau, with infinite values allowed. This is a corollary of the full stopped-history observable map equality and Mathlib lintegral_map. It does not assert full future-time independence of Q_tau.
-- source:
--   Source-faithful corollary of esscher_ae_bounded_stop_stoppedHistory_observable_map_law, pinned Mathlib lintegral_map.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_observable_map_law

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_lintegral_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s}))
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g (Y ω) ∂
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, g (Y ω) ∂
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ))))) := by sorry
