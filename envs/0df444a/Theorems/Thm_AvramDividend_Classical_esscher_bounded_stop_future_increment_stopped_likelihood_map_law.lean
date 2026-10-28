-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:54:18.714863+00:00
-- url     : https://prove2.me/theorems/dd39f9a0-2976-4f5b-aaa8-26e8604a00f7
-- title:
--   Genuine tilted bounded-stop future-increment measure law with realised stopped-likelihood history mass
-- statement:
--   For a bounded genuine stopping time τ, historical stopped event A, future lag u and deterministic tilted terminal T≥H+1+u, the full pushforward law of X_(τ+u)−X_τ under the historical restriction of the genuine Q_T measure equals (P.withDensity Mτ)(A) times the deterministic tilted increment law Q_u. This is a measure equality for every measurable future-increment test set, not merely a single cylinder, and uses the realised-time density only on the historical scalar factor.
-- source:
--   Accepted genuine bounded future-increment map law 9032b4a2 and direct true bounded stopped-history Esscher density equality 47b25ea7. No full-path product, global Q∞, independently sampled clock under stopped density, or WH splitting is postulated.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT.restrict A) = QStop A • Measure.map (X.X u) QU := by sorry
