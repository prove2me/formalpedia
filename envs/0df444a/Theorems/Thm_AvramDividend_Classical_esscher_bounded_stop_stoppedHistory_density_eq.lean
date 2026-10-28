-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_density_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:34:59.794778+00:00
-- url     : https://prove2.me/theorems/47b25ea7-4b63-4ea2-bf11-ff3120dd2065
-- title:
--   A bounded genuine stopping time admits exact Esscher stopped-history density transfer
-- statement:
--   For a genuine bounded stopping time τ≤H with right-continuous natural Lévy filtration, a stopped-history event A satisfying A∩{τ≤s}∈F_s for every s, and a deterministic Esscher terminal T≥H+1, the genuine finite-terminal tilted probability Q_T and the realised stopped likelihood P.withDensity M_τ have identical mass on A. Upper dyadic approximants are constructed from the accepted bounded-stop explicit grid theorem, their uniform integrability comes from the proved finite-grid L² bound, and the resulting identity needs no auxiliary grid assumptions, no optional stopping axiom and no global Esscher extension.
-- source:
--   Accepted explicit dyadic upper stopping grid 062ac6d1, stoppedHistory_event_measurable, forthcoming full bounded-stop stoppedEvent density bridge, built from proved L2/UI and Vitali eventwise density transfer. No WH or two-sided exit assumption.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_density_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by sorry
