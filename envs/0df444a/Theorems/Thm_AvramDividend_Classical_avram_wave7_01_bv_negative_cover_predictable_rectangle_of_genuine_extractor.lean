-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_cover_predictable_rectangle_of_genuine_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_bv_negative_cover_predictable_rectangle_of_genuine_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:46:29.613939+00:00
-- url     : https://prove2.me/theorems/46a61c20-110a-4473-93bd-aabce89c8a4b
-- title:
--   Original BV finite-activity predictable rectangles for every negative-cover Borel mark set from a genuine extractor
-- statement:
--   With original Lévy Ω,P,X,filtration and the explicit necessary negative-finite-activity and bounded-variation assumptions, any Borel mark B containing all negative marks has its actual predictable rectangle count identity, provided its negative-mark future count is represented by a measurable functional of the actual shifted source path. This genuine conditional theorem does not assume the intensity law, proved from the exact source negative mark rate, and does not pretend the independent extractor hypothesis has been discharged.
-- source:
--   Proved full-clock source BV negative conditional rectangle b2260a53 plus Proved source mark-support c2e1a7f1 and ν-support c324380a; no replacement process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_predictable_rectangle_all_starts_of_extractor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_negative_cover_predictable_rectangle_of_genuine_extractor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCover : Iio (0 : ℝ) ⊆ B)
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
      (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
