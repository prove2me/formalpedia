-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:56:15.946138+00:00
-- url     : https://prove2.me/theorems/0e9055fe-8191-4042-809f-ab34ac1360c8
-- title:
--   Arbitrary stopped-history observable has the same pushforward law under genuine terminal Esscher and realised bounded-stop likelihood
-- statement:
--   For any measurable observable Y of the actual stopped history at a bounded genuine stopping time τ, whose inverse images of all measurable test sets are adapted stopped-history events, the entire pushforward measure of Y under the genuine finite-terminal Esscher law Q_T agrees with its pushforward under the realised-time stopped likelihood P.withDensity Mτ. Equality holds as measures on any measurable target space, not only as a single event-probability identity.
-- source:
--   From accepted genuine bounded-stop stoppedHistory density equality 47b25ea7; use measure extensionality and measurable pullbacks of every test set. This does not extend Q_T to infinite horizons or identify the future law under the realised density.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ)))) := by sorry
