-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T19:21:35.601376+00:00
-- url     : https://prove2.me/theorems/4c1a5b7a-3823-4410-843a-a15e67667201
-- title:
--   Cross-terminal projective consistency of every measurable bounded-stopped-history observable under finite Esscher tilts
-- statement:
--   For a genuine bounded stopping time τ≤H, an arbitrary measurable stopped-history observable Y into any measurable target space, and two deterministic Esscher terminal horizons T₁,T₂≥H+1, the full pushforward law of Y under Q_T₁ equals its full pushforward law under Q_T₂. No ordering between T₁ and T₂ is needed. This expresses optional projective consistency for genuine stopped-history observables within the finite-terminal Esscher family and does not invoke an infinite-horizon path measure.
-- source:
--   Apply accepted arbitrary stopped-history observable map equality 0e9055fe separately at both terminal horizons, identifying both observable laws with the same realised stopped likelihood P.withDensity Mτ. No independent clock, Wiener–Hopf factor or exit identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁)
    (hT₂ : H + 1 ≤ T₂)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))) := by sorry
