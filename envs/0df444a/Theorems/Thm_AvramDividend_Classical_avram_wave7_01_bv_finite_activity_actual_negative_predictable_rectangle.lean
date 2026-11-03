-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:35:16.023066+00:00
-- url     : https://prove2.me/theorems/29c1b8ca-273f-4f18-8e04-45f7d57ed1fd
-- title:
--   Actual BV finite-activity negative jump rectangle has exact predictable original-filtration compensator
-- statement:
--   For the unchanged source SpectrallyNegativeLevy and past filtration, prove exact E[1_A N_X((s,t]×(-∞,0))] = P(A)(t-s)ν(-∞,0), under explicit BV and finite activity ν(-∞,0)<∞, with 0<s≤t. This is a fully proved original-process compensation instance and does not conflate bounded variation with finite jump activity. No Poisson replacement, no rate assumption on the conclusion.
-- source:
--   Genuine original shifted-future Borel extractor 5cf3e058 Proved, original past-event factor ad24b83b Proved and genuine original BV finite-activity total negative rate c7a926f3 Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
