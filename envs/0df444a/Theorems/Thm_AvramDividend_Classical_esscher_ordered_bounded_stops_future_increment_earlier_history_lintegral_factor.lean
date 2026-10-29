-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_future_increment_earlier_history_lintegral_factor
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_lintegral_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:03:18.606996+00:00
-- url     : https://prove2.me/theorems/00e5bd75-0f0c-4ff0-be73-d20bf9f163be
-- title:
--   Any nonnegative future-increment reward at a later bounded stop factors with the earlier stopped-history Esscher likelihood
-- statement:
--   For two genuine bounded stopping times τ≤σ≤H, any event A of the earlier stopped history and any nonnegative measurable reward g of the future increment after σ, the integral of g(X_(σ+u)−Xσ) on A under true finite-horizon Esscher Q_T equals the realised likelihood mass QStopτ(A) times the deterministic Q_u expected reward g(X_u). No finite-moment assumption is required, and the realised stopped likelihood is used only as the earlier-history mass.
-- source:
--   Derive directly from the canonically proved later-stop future-increment restricted map law b71263ed, path-measurability of the bounded stopped future increment, and pinned Mathlib lintegral_map plus lintegral_smul_measure. The later-stop map theorem is proved from genuine Q_T Markov consistency and two-stop history likelihood consistency; no Wiener–Hopf or globally independent stopped-likelihood future is assumed.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_future_increment_earlier_history_map
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_lintegral_factor
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
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω in A,
      g (X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
      Qτ A * (∫⁻ ω, g (X.X u ω) ∂QU) := by sorry
