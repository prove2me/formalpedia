-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_negative_cover_borel_mark_unconditional_rate
-- name    : AvramDividend.Classical.avram_wave7_01_bv_original_negative_cover_borel_mark_unconditional_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:29:28.131895+00:00
-- url     : https://prove2.me/theorems/6c472f2b-53a3-4715-8ac7-48083c40def6
-- title:
--   Unconditional original BV finite-negative-activity Lévy jump rectangle rate for every Borel set covering negative marks
-- statement:
--   For the actual original spectrally negative Lévy process on Ω, P, 𝓕 and its own source intrinsic jump count, assume bounded variation and explicitly finite total negative Lévy mass. Every Borel mark cell B containing (-∞,0), including all marks and all semibounded upper mark sets with nonnegative upper threshold, has exactly the unconditional jump intensity (t-s)X.ν(B) for all ordered s≤t, including the zero-start and zero-duration clocks.
-- source:
--   Proved original pointwise negative-mark support c2e1a7f1; Proved original Lévy measure negative restriction c324380a; Proved genuine finite-intensity BV all-start negative mark rate 16d87590. No proxy process, no measurable extractor assumption and no unproved imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_mark_negative_support_count
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_any_start_negative_mark_exact_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_original_negative_cover_borel_mark_unconditional_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCover : Iio (0 : ℝ) ⊆ B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
