-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
-- name    : AvramDividend.Classical.avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:59:58.410066+00:00
-- url     : https://prove2.me/theorems/557aabfa-c990-4bdc-9eff-492f4477acbf
-- title:
--   Actual intrinsic Lévy marked counting measure finite on every compact time-by-magnitude band, BV and UBV
-- statement:
--   For every original SpectrallyNegativeLevy P 𝓕 path, any finite T and δ>0, the literal intrinsic marked jump-counting measure assigns finite mass to (0,T] times the real jump-mark band {y : |y|≥δ}. This includes unbounded variation and imposes no finite Lévy activity assumption. It follows from the same-path exact count/encard representation and the pathwise finite set of genuinely large source jumps, not from sigma-finiteness of ν or a detached marked-Poisson process. It is the raw jump-measure localisation required before proving marked rectangle compensators.
-- source:
--   Proved same-path finite big-jump set and arbitrary Borel marked count=encard identity; finite subset and finite encard.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤ := by sorry
