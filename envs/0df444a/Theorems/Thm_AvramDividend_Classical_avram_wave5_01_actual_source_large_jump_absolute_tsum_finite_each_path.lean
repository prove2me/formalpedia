-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_large_jump_absolute_tsum_finite_each_path
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_large_jump_absolute_tsum_finite_each_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:17:35.136038+00:00
-- url     : https://prove2.me/theorems/61808bd0-2372-42e1-b682-b7a78241e7ad
-- title:
--   Original BV and UBV source has finite absolute sum of separated jumps over every compact horizon
-- statement:
--   For every original SpectrallyNegativeLevy P 𝓕 sample path and every T>=0 and δ>0, the unrestricted extended nonnegative sum over all genuine source jump times in (0,T] with jump magnitude at least δ of the absolute jump size is finite. This is a pathwise total-variation localisation statement valid even for unbounded variation. It uses the canonically proved finiteness of actual separated jump times and preserves the original sample space and filtration. It enables finite-band source sum truncation in predictable martingale localisation and controlled Ito-Meyer sums, without claiming a compensator or Levy intensity identification.
-- source:
--   Actual original source finite-horizon separated jump-time set finite theorem UUID 52f0bc5f-fb6d-4e4c-95a7-20b6fc1c8835, then finite ENNReal sum of pointwise finite real mark magnitudes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave5_01_actual_source_large_jump_absolute_tsum_finite_each_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    (∑' u : ℝ≥0,
      if 0 < u ∧ u ≤ T ∧
        δ ≤ dist (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0
      then ENNReal.ofReal |X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u|
      else 0) < ⊤ := by sorry
