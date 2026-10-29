-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_joint_history_increment_terminal_consistency
-- name    : AvramDividend.Classical.esscher_bounded_stop_joint_history_increment_terminal_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:45:01.767246+00:00
-- url     : https://prove2.me/theorems/fd8b103d-9b70-4cc4-a229-dcb8733143c9
-- title:
--   Cross-terminal projectivity of the entire joint law of a bounded stopped history observable and its subsequent increment
-- statement:
--   For any genuine bounded stopping time τ≤H, any measurable stopped-history observable Y, any u≥0, and arbitrary finite Esscher horizons T₁,T₂≥H+1+u, the entire joint pushforward distribution of (Y,X_(τ+u)−Xτ) under Q_T₁ and Q_T₂ agrees. No ordering between T₁,T₂ or global Esscher path measure is required. The equality holds on arbitrary measurable sets of β×ℝ, not merely rectangles.
-- source:
--   Apply canonically accepted full genuine bounded stopped-history/future-increment product law 2ae6f49a at both terminal horizons. Both joint laws equal the same product of stopped-likelihood history marginal and deterministic Q_u increment marginal; no Wiener–Hopf or realised-time future independence assumed.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_future_increment_joint_product

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_joint_history_increment_terminal_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T₁ T₂ : ℝ≥0) (hT₁ : H + 1 + u ≤ T₁)
    (hT₂ : H + 1 + u ≤ T₂)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT₁ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))
    let QT₂ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
      X.X (τ ω + u) ω - X.X (τ ω) ω)) QT₁ =
    Measure.map (fun ω : Ω => (Y ω,
      X.X (τ ω + u) ω - X.X (τ ω) ω)) QT₂ := by sorry
