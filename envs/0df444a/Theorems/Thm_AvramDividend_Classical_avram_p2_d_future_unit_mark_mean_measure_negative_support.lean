-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_unit_mark_mean_measure_negative_support
-- name    : AvramDividend.Classical.avram_p2_d_future_unit_mark_mean_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:48:03.284375+00:00
-- url     : https://prove2.me/theorems/6c4cc971-e673-4068-93fe-fd06ca400691
-- title:
--   Original unit-time marked mean measure is intrinsically supported on strict negative marks
-- statement:
--   A single actual original count-derived Borel mark mean measure ρ represents all original unit-time intrinsic marked jump-count expectations and is supported on strictly negative marks: for every Borel B, ρ(B)=ρ(B∩(-∞,0)). It makes no assumed identification with the original Lévy ν.
-- source:
--   Use Proved original first-unit mark mean measure 32d3702f, then apply Proved literal original source rectangle negative-mark restriction and lintegral_congr, preserving P and original sample X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_unit_mark_mean_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ,
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P)) ∧
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = ρ (B ∩ Iio (0 : ℝ))) := by sorry
