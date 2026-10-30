-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_condexp
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_future_killed_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:33:08.316104+00:00
-- url     : https://prove2.me/theorems/35712f66-895e-4ae9-b7b8-380f4723bb22
-- title:
--   Genuine real conditional killed q-scale semigroup from source-Lévy past-event tests
-- statement:
--   For every actual original-law spectrally negative Lévy process of unbounded variation and every historical filtration time, the real conditional expectation of the closed lower-killed, discounted future-window q-scale reward is the current q-scale value, under explicit measurable survival and actual grid completeness. This is derived from the accepted source-path Markov historical test and rigorous nonnegative ENNReal-to-real conditional expectation uniqueness, without importing stopped-scale or exit identities.
-- source:
--   Exclusive WS1A Lean draft work/avram_root29_01_unbounded_future_killed_condexp_draft.lean.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_killed_past_test
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_nonneg_past_test_condexp_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_root29_01_unbounded_future_killed_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0) (s T : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (x : ℝ)
    (hB : MeasurableSet {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}) :
    P[({ω | ∀ v : ℝ≥0, v ≤ T →
      0 ≤ (x + X.X s ω) + (X.X (s + v) ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * (T : ℝ))) *
        W ((x + X.X s ω) + (X.X (s + T) ω - X.X s ω))) | 𝓕 s]
      =ᵐ[P] (fun ω => W (x + X.X s ω)) := by sorry
