-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_future_increment_earlier_history_map
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:48:37.23578+00:00
-- url     : https://prove2.me/theorems/b71263ed-71ca-458e-9717-74566d443b3b
-- title:
--   Fresh future increment at a later bounded stop factors against the earlier stopping-time Esscher likelihood history
-- statement:
--   For two genuine stopping times τ≤σ≤H, any event A measurable in the earlier stopped history at τ, any u≥0 and actual finite-terminal Esscher Q_T with T≥H+1+u, the full pushforward law of the future increment X_(σ+u)−Xσ under Q_T restricted to A factors as the earlier stopped-likelihood mass (P.withDensity Mτ)(A) times the deterministic Q_u law of X_u. The later stop's future law is thus independent of the earlier history under the genuine terminal tilt, without assuming any strong Markov property under QStopτ or a global Q∞.
-- source:
--   The accepted bounded-stop mixed increment map law dd39f9a0 applies at later σ because τ≤σ makes each earlier stopped-history event adapted at σ. The accepted ordered-stops Esscher likelihood consistency 41ca6a41 then transfers its historical scalar from QStopσ to QStopτ. No Wiener–Hopf, killed-scale or exit identity.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_likelihood_history_consistency

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_map
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hAτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (σ ω + u) ω -
        X.X (σ ω) ω) (QT.restrict A) =
      Qτ A • Measure.map (X.X u) QU := by sorry
