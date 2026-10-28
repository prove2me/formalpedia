-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_charFun
-- name    : AvramDividend.Classical.cross_levy_path_event_law_of_equal_charFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:48:43.083878+00:00
-- url     : https://prove2.me/theorems/91c154e0-de4a-409b-85a7-915367ec81dd
-- title:
--   Matching Lévy characteristic functions transfer every measurable whole-path event
-- statement:
--   Two spectrally negative Lévy processes defined on potentially unrelated probability spaces have matching whole-path probabilities for every measurable event in the coordinate-product real-valued path space, provided their time-marginal characteristic functions agree. Prove path map measurability coordinatewise, apply the Proved whole-path law equality, then evaluate the common path law on the event using Measure.map_apply. This is the genuine sample-space transfer interface for a measurable canonical jump-count zero event.
-- source:
--   Proved AvramDividend.Classical.cross_levy_whole_path_law_of_equal_charFun [23820eb7-356e-472a-81f3-449f65415c15] and pinned Mathlib Measure.map_apply.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_charFun

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_path_event_law_of_equal_charFun
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (Measure.map (X.X t) P₁) ξ =
      charFun (Measure.map (Y.X t) P₂) ξ)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by sorry
