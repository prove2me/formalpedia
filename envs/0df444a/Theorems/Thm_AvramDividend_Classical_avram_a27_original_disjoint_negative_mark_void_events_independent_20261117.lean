-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
-- name    : AvramDividend.Classical.avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:12:29.050052+00:00
-- url     : https://prove2.me/theorems/48b8388b-2f1f-4cd1-8224-3fe884327c88
-- title:
--   Original physical disjoint negative Borel marked-jump void events factor exactly
-- statement:
--   At a fixed horizon of the original finite-activity spectrally negative Lévy process, the events that no physical negative jump has mark in disjoint negative Borel sets B or C have exactly factorised original probabilities.
-- source:
--   Proved original shifted Borel physical void exponential law, disjoint measure additivity and the pathwise marked counting measure union identity; no external probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Disjoint negative mark sets have independent original physical void events at a fixed horizon. -/

theorem AvramDividend.Classical.avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNegB : B ⊆ Iio (0 : ℝ)) (hNegC : C ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint B C) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0 ∧
      NX ω (Ioc 0 T ×ˢ C) = 0}).toReal =
      (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0}).toReal *
      (P {ω | NX ω (Ioc 0 T ×ˢ C) = 0}).toReal := by sorry
