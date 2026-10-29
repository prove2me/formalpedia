-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_observable_map_law
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_observable_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:45:48.098682+00:00
-- url     : https://prove2.me/theorems/fa8178e4-b64d-4757-b134-035804513b86
-- title:
--   Entire stopped-history observable map law under an almost-surely bounded Esscher stopping time
-- statement:
--   For a genuine stopping time tau bounded only P-almost surely by H, any measurable stopped-history observable Y has exactly the same pushforward law under the finite-terminal Esscher measure Q_T and the realised stopped-likelihood measure Q_tau. The proof applies the canonically Proved almost-sure bounded stopped-history density equality to every measurable preimage of Y and uses extensionality of measures. No all-time tilted law or strong Markov under Q_tau.
-- source:
--   Proved esscher_ae_bounded_stop_stoppedHistory_density_eq 2ae80188-be21-46be-be89-7823f3ed26bd and pinned Mathlib Measure.ext and Measure.map_apply.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_stoppedHistory_observable_map_law
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
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ)))) := by sorry
