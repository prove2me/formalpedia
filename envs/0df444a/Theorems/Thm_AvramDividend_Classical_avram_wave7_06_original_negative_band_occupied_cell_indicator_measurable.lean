-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:16:53.928359+00:00
-- url     : https://prove2.me/theorems/bc862522-be87-4777-a6d3-d26f1072cc84
-- title:
--   Original negative-band occupied-cell indicator is measurable on the same sample space
-- statement:
--   The one-zero indicator that the genuine source X has a negative-band jump in a shifted time cell is measurable on the original Ω. This discharges the explicit cell measurability condition in the Proved finite-grid mean theorem and the source uniform-grid assembly, without assuming an external Poisson law.
-- source:
--   W7-06 measurability interface using the already accepted original future Borel-mark void event measurability 0b92926a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_indicator_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    Measurable (fun ω : Ω =>
      ({ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
        (fun _ => (1 : ENNReal)) ω) := by sorry
