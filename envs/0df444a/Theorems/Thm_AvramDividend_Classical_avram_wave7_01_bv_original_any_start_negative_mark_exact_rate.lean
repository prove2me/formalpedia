-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_any_start_negative_mark_exact_rate
-- name    : AvramDividend.Classical.avram_wave7_01_bv_original_any_start_negative_mark_exact_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:57:50.306345+00:00
-- url     : https://prove2.me/theorems/16d87590-ebcd-4b85-8ea0-920abbcb606f
-- title:
--   Original BV finite-activity negative-jump Lévy mean rate holds for every ordered time interval including zero
-- statement:
--   For the actual bounded-variation SpectrallyNegativeLevy with explicit finite negative Lévy intensity, and any s≤t including s=0, t=s and the zero interval, the expected literal intrinsic negative-jump count over (s,t] equals (t−s)ν((−∞,0)). This joins the separately Proved positive-start and zero-start original-source cases, ensuring endpoints are handled and BV is never silently equated with finite activity.
-- source:
--   Combine Proved original positive-start interval c7a926f3-2b09-4614-ae82-f607fc1a0058 and newly published zero-start child da7b127b-7afe-429f-9906-dee7b44d2999; handle the zero-duration case by empty interval count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_zero_start_negative_mark_exact_rate

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_original_any_start_negative_mark_exact_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
