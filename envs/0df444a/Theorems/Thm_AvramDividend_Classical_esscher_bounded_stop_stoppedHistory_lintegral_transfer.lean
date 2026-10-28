-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_lintegral_transfer
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_lintegral_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T19:06:11.415871+00:00
-- url     : https://prove2.me/theorems/43424b65-683e-4f05-9ea9-e51576c21289
-- title:
--   Transfer of arbitrary nonnegative measurable stopped-history rewards between terminal and stopped Esscher laws
-- statement:
--   At any genuine bounded Lévy stopping time τ≤H, every nonnegative extended-real stopped-history observable F has the same full Lebesgue integral under the genuine finite-terminal tilted Q_T and the realised stopped density P.withDensity Mτ, provided T≥H+1 and all measurable level events of F satisfy the stopped-history adaptedness condition. This is an integral-level optional Esscher change of measure, without imposing independent increments under the realised-time density.
-- source:
--   Accepted bounded-stop stoppedHistory observable pushforward law, followed by the pinned Mathlib `lintegral_map` for measurable F and the identity observable. Depends neither on Wiener–Hopf splitting nor on the global Esscher law.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_lintegral_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFstopped : ∀ (B : Set ℝ≥0∞), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((F ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    ∫⁻ ω, F ω ∂(P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    ∫⁻ ω, F ω ∂(P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by sorry
