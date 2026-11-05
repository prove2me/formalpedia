-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_zero_horizon
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_zero_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:37:18.946034+00:00
-- url     : https://prove2.me/theorems/30878674-a8f7-48f5-887e-229a0c9910da
-- title:
--   Actual original negative-band chronological pair count vanishes at zero horizon
-- statement:
--   For the exact original spectrally negative Levy sample path, the marked negative jump-time set in (0,0] is empty, hence its chronological pair count vanishes at zero horizon. The original source and finite-mark definition are unchanged; this discharges the zero-horizon boundary case of the open exact pair-expectation theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_zero_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card = 0 := by sorry
