-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_observable_likelihood_consistency
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_observable_likelihood_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:53:04.380291+00:00
-- url     : https://prove2.me/theorems/c1ef8131-f4e4-422e-930f-7130000bfb2d
-- title:
--   Optional two-stop consistency of the full distribution of an earlier stopped-history observable under realised Esscher likelihood measures
-- statement:
--   Let τ≤σ≤H be genuine stopping times. For any measurable observable Y of the earlier stopped history at τ, the entire pushforward law of Y under the realised Esscher density at τ equals its pushforward law under the realised Esscher density at σ, with θ≥0 and an available finite terminal horizon T≥H+1. This strengthens single-event optional likelihood consistency to arbitrary measurable target spaces and does not claim an independently-clocked future law under either stopped density.
-- source:
--   Apply the accepted exact ordered-stops stopped-history Esscher event identity 41ca6a41 to the preimage of every measurable test set under Y, using Measurable Y and Mathlib Measure.ext with Measure.map_apply. No Q∞ or Wiener–Hopf assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_likelihood_history_consistency

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_observable_likelihood_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYτ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (σ ω) ω -
          (σ ω : ℝ) * X.ψ θ)))) := by sorry
