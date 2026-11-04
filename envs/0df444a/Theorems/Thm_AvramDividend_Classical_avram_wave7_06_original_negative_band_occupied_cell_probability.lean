-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_probability
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:02:12.127683+00:00
-- url     : https://prove2.me/theorems/e0f78a6a-4e5e-4112-8890-12ded93bebf5
-- title:
--   Original negative-band occupied-cell probability equals the complement of stationary void
-- statement:
--   For the actual intrinsic X jump counting measure and every negative band, the source P probability that a shifted interval contains at least one mark equals one minus the original P zero-count probability on the corresponding origin interval. Uses source stationary void law, source measurability and probability normalisation; a direct ingredient for the expected number of occupied grid cells.
-- source:
--   W7-06 actual finite-grid one-cell void/occupation bridge; directly imports original marked void stationarity and source count-event measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0} =
    1 - P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
