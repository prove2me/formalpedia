-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:30:29.741842+00:00
-- url     : https://prove2.me/theorems/d982b66d-c696-4a15-8f26-7eb4c42c93a5
-- title:
--   Exact original negative-band no-jump event equals zero intrinsic marked count
-- statement:
--   On the original sample path of every spectrally negative Lévy process, the absence of any jump of magnitude at least 1/(n+1) in (0,T] is logically equivalent, path by path, to zero mass of the genuine intrinsic jump counting measure on the exact negative mark band. No auxiliary process, probability approximation, or BV assumption is used.
-- source:
--   Source-faithful deterministic pathwise bridge for Avram mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. It converts the literal threshold event into a marked zero-count question and exposes the remaining probabilistic Poisson law independently; adapted from existing Proved intrinsic rectangle encard identity f6336d40-2d19-444f-bacd-83724316de67.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_iff_intrinsic_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    (∀ u : ℝ≥0, u ∈ Ioc 0 T →
      ¬ (X.X u ω + (1 / ((n : ℝ) + 1)) ≤
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ↔
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by sorry
