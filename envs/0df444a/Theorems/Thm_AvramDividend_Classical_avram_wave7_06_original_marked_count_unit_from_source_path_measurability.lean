-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_marked_count_unit_from_source_path_measurability
-- name    : AvramDividend.Classical.avram_wave7_06_original_marked_count_unit_from_source_path_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:01:49.231183+00:00
-- url     : https://prove2.me/theorems/c07f04d5-c866-425d-88a2-cb0ec7eba3fa
-- title:
--   Original marked jump count nonzero implies at least one from source path measurability
-- statement:
--   For the actual sample-path marked jump measure of the source process X, assuming the fixed-path mark map and nonzero-jump time set are Borel measurable, its nonzero value on the exact shifted negative-band rectangle is at least one. This follows from count_measure.map/restrict, a measurable preimage and nonzero enhanced cardinality. Does not rely on an auxiliary Lévy process or a Poisson law; future consumers must prove the two pathwise measurability assumptions from source càdlàg regularity.
-- source:
--   Wave7-06 original count-unit prerequisite for source occupied probability ≤ first moment

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_marked_count_unit_from_source_path_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (hMark : ∀ ω : Ω, Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (hJump : ∀ ω : Ω, MeasurableSet {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0 →
    1 ≤ ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by sorry
