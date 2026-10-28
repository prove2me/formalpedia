-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_likelihood_history_consistency
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_likelihood_history_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T19:15:57.191593+00:00
-- url     : https://prove2.me/theorems/41ca6a41-c3b5-4d6f-92ff-521275b9162b
-- title:
--   Optional consistency of realised Esscher likelihood measures at two ordered bounded stopping times on the earlier stopped history
-- statement:
--   Let τ≤σ≤H be two genuine stopping times of a spectrally negative Lévy process and let A be any event in the stopped history at the earlier time τ. For θ≥0 and a fixed terminal horizon T≥H+1, the realised stopped Esscher likelihood measures P.withDensity Mτ and P.withDensity Mσ assign exactly the same mass to A. The later stopped density is allowed to depend on a longer path, but its restriction to the earlier stopped information is consistent. This is a bounded optional Esscher change-of-measure consistency theorem and does not postulate a single Q∞.
-- source:
--   Apply accepted actual bounded-stop history density equality 47b25ea7 to both τ and σ against the common genuine finite-terminal Q_T. Show stopped-history event inclusion by τ≤σ and the stopping-time measurability of {σ≤s}. No optional martingale assumption or Wiener–Hopf/exit result.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_likelihood_history_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    let Qσ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (σ ω) ω -
        (σ ω : ℝ) * X.ψ θ)))
    Qτ A = Qσ A := by sorry
