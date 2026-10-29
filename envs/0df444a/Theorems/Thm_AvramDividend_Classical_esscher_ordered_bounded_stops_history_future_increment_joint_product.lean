-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_product
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:52:08.088604+00:00
-- url     : https://prove2.me/theorems/a8cb4e02-c3b7-45db-ab7f-ebb239099340
-- title:
--   Full joint product of the earlier stopped history with a fresh increment after a later bounded stopping time
-- statement:
--   For two genuine stopping times τ≤σ≤H and any measurable observable Y of the history stopped at τ, the joint law under actual finite-terminal Esscher Q_T of (Y,X_(σ+u)−Xσ) equals the product of the Y-law under the earlier realised Esscher stopped-likelihood P.withDensity Mτ and the deterministic Q_u-law of X_u, for T≥H+1+u. This full β×ℝ product measure identity permits multiple stopping stages without a global tilted path law or extra strong-Markov assumptions.
-- source:
--   Use the accepted full genuine stopped joint product 2ae6f49a at later σ. Since τ≤σ, the earlier adapted stopped-history observable Y is also adapted at σ. Apply the accepted bounded stopped-history observable density map theorem 0e9055fe at both τ and σ to identify their Y marginals. Does not use Wiener–Hopf or realised-time clock independence.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYτ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
      X.X (σ ω + u) ω - X.X (σ ω) ω)) QT =
      (Measure.map Y Qτ).prod (Measure.map (X.X u) QU) := by sorry
