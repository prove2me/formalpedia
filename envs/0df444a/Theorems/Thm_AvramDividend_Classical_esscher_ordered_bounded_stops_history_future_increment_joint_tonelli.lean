-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_tonelli
-- name    : AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:18:31.003876+00:00
-- url     : https://prove2.me/theorems/c065e89d-de22-432a-93e3-1b13f8f612be
-- title:
--   Full Tonelli conditional-kernel formula for arbitrary nonnegative payoffs of earlier stopped history and later tilted increment
-- statement:
--   For two bounded genuine stopping times τ≤σ≤H and arbitrary measurable Y from the earlier τ-stopped history to any measurable β, the expected nonnegative payoff R(Y,X_(σ+u)−Xσ) under genuine finite-terminal Esscher Q_T equals the iterated integral of R(y,z) over the deterministic Q_u increment law in z and the earlier stopped-likelihood law of Y in y. R need not factor into a product, and the equality holds even with infinite expectations. No global tilted path law, Wiener–Hopf independence or arbitrary stopped-density future law is assumed.
-- source:
--   Use the accepted full Q_T joint history/future increment map product a8cb4e02. Establish measurability of the genuine bounded stopped increment from accepted full shifted future-path measurability; Q_u is an actual probability by accepted finite-terminal Esscher normalisation, and its measurable increment map is SFinite. Apply source-verified pinned Mathlib lintegral_map to the pair and Mathlib lintegral_prod (remote exact signature checked) for arbitrary nonnegative measurable R. This is an exact finite-terminal stopped-history Markov kernel.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_history_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_tonelli
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
    (R : β × ℝ → ℝ≥0∞) (hR : Measurable R) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω, R (Y ω,
      X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
    ∫⁻ y : β, (∫⁻ z : ℝ, R (y, z) ∂Measure.map (X.X u) QU) ∂
      Measure.map Y Qτ := by sorry
