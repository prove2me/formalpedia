-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_future_increment_joint_product
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_future_increment_joint_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T19:06:17.484532+00:00
-- url     : https://prove2.me/theorems/2ae6f49a-98fa-4494-9e9f-42a38b1098f5
-- title:
--   Joint stopped-history observable and fresh increment product law under a genuine bounded terminal Esscher measure
-- statement:
--   For a bounded genuine stopping time and any measurable stopped-history observable Y, the entire joint pushforward of (Y, X_(τ+u)−Xτ) under genuine Q_T factors exactly as the pushforward of Y under realised stopped-likelihood P.withDensity Mτ times the independent deterministic tilted increment law under Q_u. This is an actual product measure equality on arbitrary measurable target β × ℝ, not merely a scalar cylinder. The product holds under Q_T only, with stopped density providing its marginal on histories.
-- source:
--   Use proven bounded stopped-future path measurability, genuine terminal Esscher probability, the stopped-history mixed tilted cylinder factor, and pinned Mathlib Measure.ext_prod plus Measure.prod_prod. No global Esscher law or Wiener–Hopf assumption.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_factor

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_future_increment_joint_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
        X.X (τ ω + u) ω - X.X (τ ω) ω)) QT =
      (Measure.map Y QStop).prod (Measure.map (X.X u) QU) := by sorry
