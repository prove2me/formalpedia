-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_terminal_consistency
-- name    : AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_terminal_consistency
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T19:18:39.347979+00:00
-- url     : https://prove2.me/theorems/9e5e284c-d332-49d9-a478-1ddd1c60512f
-- title:
--   True bounded-stopping projective consistency across any two finite Esscher terminal horizons
-- statement:
--   For any genuine bounded stopping time τ≤H and any event A observable at that stopped history, two actual finite-terminal Esscher probabilities Q_T₁ and Q_T₂ have identical masses on A whenever both terminal times are at least H+1. This is finite-horizon projective consistency on the optional stopped sigma information, with no infinite-path Esscher measure assumed or constructed.
-- source:
--   Apply the accepted direct bounded stopped-history density equality 47b25ea7 separately at T₁ and T₂, matching both historical masses with the same realised stopped density P.withDensity Mτ. No global Q∞, exit identity or Wiener–Hopf independence.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_terminal_consistency
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁)
    (hT₂ : H + 1 ≤ T₂)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))) A := by sorry
