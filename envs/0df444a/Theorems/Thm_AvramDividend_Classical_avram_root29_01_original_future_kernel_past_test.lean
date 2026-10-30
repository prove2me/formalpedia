-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test
-- name    : AvramDividend.Classical.avram_root29_01_original_future_kernel_past_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:14:29.774272+00:00
-- url     : https://prove2.me/theorems/0611e261-f045-4fb5-a53c-a42f06995418
-- title:
--   Source-original Lévy future-kernel factorisation tested against arbitrary past event
-- statement:
--   For a true spectrally negative Lévy P-law, arbitrary F_s-measurable statistic H and event A, and every measurable nonnegative payoff of the whole future increment path, prove equality of the A-restricted original-P lintegral and the A-restricted integral against the genuine original-P law of the full path. This source-specific past-test Markov kernel identity is a noncircular prerequisite for conditional expectation of a random-reserve killed q-scale reward; no killed martingale or two-sided exit conclusion is assumed.
-- source:
--   Independent full-path historic past-test derivation using Proved 77ced690, measurable history with Bool event flag, exact Markov–Tonelli and measurable right-kernel lintegral. Lean source work/avram_root29_01_original_future_kernel_past_test_draft.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_original_future_kernel_past_test
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → E)
    (hH : Measurable[𝓕 s] H)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (H ω, fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (H ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by sorry
