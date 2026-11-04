-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_deficit_le_source_first_moment_of_unit_count
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_deficit_le_source_first_moment_of_unit_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:47:18.2865+00:00
-- url     : https://prove2.me/theorems/c9c21e66-1720-4255-883a-51c59503028a
-- title:
--   Original negative-band occupied probability bounded by source marked count mean
-- statement:
--   For the actual X marked jump count in a shifted negative cutoff rectangle, assuming the elementary unit-count property (any nonzero count is at least one), the original probability of at least one jump is bounded by its expected count. Uses the source Borel void-event measurability, indicator integral and monotone lintegral. No Poisson law or compensator assumed; the unit-count hypothesis is explicit and must subsequently be discharged from the source count measure.
-- source:
--   W7-06 source L1 occupancy intensity upper bound; isolates pathwise counting-unit fact from Lévy triplet rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_deficit_le_source_first_moment_of_unit_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (hUnit : ∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
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
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) :
    P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} ≤
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ∂P) := by sorry
