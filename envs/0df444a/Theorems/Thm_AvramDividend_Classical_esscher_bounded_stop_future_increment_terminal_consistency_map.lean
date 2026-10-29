-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_terminal_consistency_map
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_terminal_consistency_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:44:09.998224+00:00
-- url     : https://prove2.me/theorems/20c584ce-2dac-474c-b76f-e0d90930c794
-- title:
--   Cross-terminal projective consistency of full bounded stopped-future-increment pushforward laws
-- statement:
--   For a genuine bounded Lévy stopping time τ≤H, a stopped-history event A, a lag u≥0 and any deterministic Esscher terminal times T₁,T₂≥H+1+u, the full pushforward law of the stopped future increment X_(τ+u)−Xτ under Q_T₁ restricted to A equals its law under Q_T₂ restricted to A. This is finite-horizon projective consistency for every measurable future-increment test, with no global Esscher path law or required ordering between T₁ and T₂.
-- source:
--   Apply canonically accepted mixed bounded-stop future-increment map law dd39f9a0 separately at T₁ and T₂. Each side equals the same realised stopped-history mass QStop(A) times the deterministic Q_u increment law; no independence under QStop or Wiener–Hopf theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_terminal_consistency_map
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T₁ T₂ : ℝ≥0) (hT₁ : H + 1 + u ≤ T₁)
    (hT₂ : H + 1 + u ≤ T₂)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT₁ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))
    let QT₂ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₁.restrict A) =
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₂.restrict A) := by sorry
