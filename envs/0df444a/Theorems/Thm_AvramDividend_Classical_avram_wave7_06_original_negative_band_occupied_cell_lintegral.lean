-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_lintegral
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:06:33.222192+00:00
-- url     : https://prove2.me/theorems/c5c26c2b-a76e-4198-add0-fd8cda8c66c7
-- title:
--   Expected original negative-band occupied-cell indicator equals one minus stationary void probability
-- statement:
--   For the actual original X jump count, the lintegral of the 0/1 indicator that a shifted time cell contains a negative-band jump equals one minus the original stationary void probability. This converts the Proved source occupied-cell event probability into the per-cell expectation required by the finite-grid L1/Poisson intensity derivation.
-- source:
--   W7-06 original source same-path occupied-cell mean, pins MeasureTheory.lintegral_indicator_one and source void measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_occupied_cell_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ) :
    (let E : Set Ω := {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}
     (∫⁻ ω, E.indicator (fun _ => (1 : ENNReal)) ω ∂P) =
       1 - P {ω : Ω |
         ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
         (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) := by sorry
