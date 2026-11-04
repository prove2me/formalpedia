-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_mixed_rectangles_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_mixed_rectangles_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:19:59.424393+00:00
-- url     : https://prove2.me/theorems/8d8e3ff4-33e3-422a-b157-87c99f3a9b51
-- title:
--   Exact original Lévy countable mixed-rectangle weighted Tonelli identity
-- statement:
--   Countable Tonelli interchange for varying genuine original Lévy marked jump rectangles with nonnegative measurable weights, including infinite expectations. This supplies the countable simple-rectangle limit interface without identifying any Lévy ν-rate.
-- source:
--   Already-Proved original intrinsic rectangle measurability and Mathlib lintegral_finset_sum/lintegral_tsum; no source ν-rate assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_mixed_rectangles_lintegral
    {ι Ω : Type*} [Countable ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable (H i)) :
    (∫⁻ ω, (∑' i : ι, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i))) ∂P) =
    ∑' i : ι, (∫⁻ ω, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i)) ∂P) := by sorry
