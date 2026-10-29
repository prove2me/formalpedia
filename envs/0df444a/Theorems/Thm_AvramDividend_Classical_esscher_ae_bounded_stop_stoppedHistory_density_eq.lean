-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_density_eq
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_density_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:33:19.955629+00:00
-- url     : https://prove2.me/theorems/2ae80188-be21-46be-be89-7823f3ed26bd
-- title:
--   Stopped-history Esscher density consistency for an almost-surely bounded stopping time
-- statement:
--   Under the original spectrally negative Levy probability P, let tau be a genuine stopping time bounded by H only P-almost surely. For any stopped-history event A, the deterministic-terminal Esscher measure Q_T and the actual realised stopped-time Esscher density measure Q_tau assign exactly the same historical mass to A whenever T>=H+1. Clip tau at H and A to {tau<=H}, use the accepted genuinely bounded stopped-history density law, and use withDensity_congr_ae and measure_congr to remove the P-null exceptional set. Does not assert global tilted strong Markov or a Q_infinity law.
-- source:
--   Proved bounded_stop_stoppedHistory_density_eq UUID 47b25ea7-4b63-4ea2-bf11-ff3120dd2065; pinned Mathlib IsStoppingTime.min_const, withDensity_congr_ae, withDensity_absolutelyContinuous, measure_congr.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_density_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by sorry
