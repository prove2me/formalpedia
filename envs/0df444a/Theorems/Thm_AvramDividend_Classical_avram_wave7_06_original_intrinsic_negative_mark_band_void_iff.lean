-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:23:11.313734+00:00
-- url     : https://prove2.me/theorems/9c6a5cc1-9072-4dc0-b6b8-47c1e54c4f0a
-- title:
--   Every measurable negative mark band has zero original intrinsic count iff no source jump enters it
-- statement:
--   For the actual original X path, any measurable jump-mark set B strictly below zero has zero intrinsic marked-count measure on (0,T] times B if and only if every positive-time jump up to T avoids B. This includes arbitrary small-jump truncation bands and requires no auxiliary process or probabilistic assumption.
-- source:
--   Source-specific marked jump rectangle-count identity supporting the wave7-06 original small-jump L² and L¹ limit, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; generalises the accepted fixed-cutoff d982b66d-c696-4a15-8f26-7eb4c42c93a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_mark_band_void_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ)
    (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∉ B) ↔
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) = 0 := by sorry
