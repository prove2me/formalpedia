-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
-- name    : AvramDividend.Classical.avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:43:32.149786+00:00
-- url     : https://prove2.me/theorems/7d20101a-7c9a-4f85-8e1f-5e4eb817af03
-- title:
--   Original future Lévy increment conditional expectation given its own past equals source mean
-- statement:
--   For the actual canonical Lévy process, conditional expectation under original P of X_(s+t)-X_s given the original filtration 𝓕_s equals the original mean E[X_t], provided X_t is integrable. The argument uses the original indepIncrements field, generated future-increment sigma algebra, filtration containment, and the pinned conditional-expectation independence theorem. No auxiliary process or changed filtration.
-- source:
--   W7-06 original-filtration conditional L¹ martingale difference core precursor to stopped marked compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_future_increment_condExp_of_source_past_eq_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    P[(fun ω => X.X (s + t) ω - X.X s ω) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, X.X t ω ∂P) := by sorry
