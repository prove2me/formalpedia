-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_predictable_rectangle_all_starts_of_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_bv_negative_mark_predictable_rectangle_all_starts_of_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:07:23.80766+00:00
-- url     : https://prove2.me/theorems/b2260a53-529b-4321-8e44-0ba6889c3cf5
-- title:
--   Full-clock original BV finite-activity negative-mark predictable rectangle from genuine measurable extractor
-- statement:
--   On the exact original spectrally negative Lévy Ω,P,𝓕,X, under BV plus explicit finite negative-jump activity, prove the genuine predictable marked rectangle identity E[1_A N_X((s,t]×(-∞,0))]=P(A)(t−s)ν((−∞,0)) for all s≤t including s=0 and zero duration. The only remaining explicit premise is a correctly proved measurable same-original-future-path extractor F; it is not silently asserted. This extends the Proved strictly-positive-start special case b40844ea.
-- source:
--   Apply Proved source past-event factorisation ad24b83b-aa01-4fe1-a792-380fdb3e7329 and newly published full-clock original finite-BV negative-mark rate avram_wave7_01_bv_original_any_start_negative_mark_exact_rate; then rewrite and use multiplication associativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_any_start_negative_mark_exact_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_negative_mark_predictable_rectangle_all_starts_of_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
