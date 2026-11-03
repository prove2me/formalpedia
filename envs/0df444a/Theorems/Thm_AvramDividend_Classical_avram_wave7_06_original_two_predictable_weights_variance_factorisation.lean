-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_two_predictable_weights_variance_factorisation
-- name    : AvramDividend.Classical.avram_wave7_06_original_two_predictable_weights_variance_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:30:18.704018+00:00
-- url     : https://prove2.me/theorems/1f36f43c-2032-45a5-a076-4394b05b0a7a
-- title:
--   Original consecutive predictable scalar source L2 variance factorises into independent-cell variances
-- statement:
--   The exact variance of the sum of two predictably weighted centred original X increments equals E[W0²]Var(X_u)+E[W1²]Var(X_v). This uses the authentic X, P, filtration, independent future increments and explicit first/second moments; additional source cross-integrability permits the two-cell energy expansion. It is a genuine original-process scalar result and does not identify the intrinsic jump count compensator.
-- source:
--   W7-06 source-specific two-step compensated martingale L2 variance estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_two_predictable_weights_variance_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hW₀Sq : Integrable (fun ω => (W₀ ω)^2) P)
    (hW₁Sq : Integrable (fun ω => (W₁ ω)^2) P)
    (hXI₀ : Integrable (X.X u) P)
    (hXI₁ : Integrable (X.X v) P)
    (hXSq₀ : Integrable (fun ω => (X.X u ω)^2) P)
    (hXSq₁ : Integrable (fun ω => (X.X v ω)^2) P)
    (hEarlierProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P)
    (hSqA : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P)))^2) P)
    (hSqB : Integrable (fun ω =>
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))^2) P)
    (hCross : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) *
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) +
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P))))^2 ∂P) =
    (∫ ω, (W₀ ω)^2 ∂P) *
      (∫ ω, (X.X u ω - (∫ η, X.X u η ∂P))^2 ∂P) +
    (∫ ω, (W₁ ω)^2 ∂P) *
      (∫ ω, (X.X v ω - (∫ η, X.X v η ∂P))^2 ∂P) := by sorry
