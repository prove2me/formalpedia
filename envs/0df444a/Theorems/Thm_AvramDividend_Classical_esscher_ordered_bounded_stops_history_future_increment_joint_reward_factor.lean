-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_reward_factor
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:12:19.557145+00:00
-- url     : https://prove2.me/theorems/110c3c4c-1a72-4fa9-9333-5c1e2276be65
-- title:
--   Nonnegative product rewards of earlier stopped history and later fresh Esscher increment factor exactly
-- statement:
--   For τ≤σ≤H genuine bounded stopping times, an arbitrary adapted earlier-history observable Y to any measurable space β, and any nonnegative measurable rewards f(Y) and g(X_(σ+u)−Xσ), the genuine finite-terminal Esscher Q_T expected product equals the stopped Esscher likelihood expectation of f(Y) at τ times the deterministic Q_u expected reward of g(X_u). The equality is valid in extended nonnegative reals including infinite expectations; no global tilted path law or WH independence is assumed.
-- source:
--   Apply accepted full genuine ordered-stop joint product law a8cb4e02 to pushforward pair (Y,Δσ(u)). The pinned Mathlib lintegral_prod_mul theorem (private exact signature checked at revision 0df444a) factors any two nonnegative measurable reward tests. The second marginal map X_u Q_u is S-finite because accepted finite-terminal Esscher unit probability is preserved by the measurable increment map. Convert both marginals with lintegral_map. The proof requires no additional strong Markov assumption.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_reward_factor
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
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s}))
    (f : β → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω, f (Y ω) *
      g (X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
    (∫⁻ ω, f (Y ω) ∂Qτ) *
      (∫⁻ ω, g (X.X u ω) ∂QU) := by sorry
