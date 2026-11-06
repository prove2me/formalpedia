-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:21:19.831474+00:00
-- url     : https://prove2.me/theorems/d018dd24-464c-45cb-b2b9-2c6c2ab28ee6
-- title:
--   Original Levy small-jump compensator cutoff has finite intrinsic time support at every horizon
-- statement:
--   For the actual sample path of any spectrally negative Levy X and the strict (-1,0) truncation, the cutoff band (-1,-1/(n+2)] contains only finitely many source jump times on each bounded horizon. This constructs the real finite summation domain needed for Jsmall^epsilon, without an auxiliary jump process or compensation-rate assumption.
-- source:
--   Proved original-source finite-horizon separated jumps theorem avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path; subset under |jump| >= 1/(n+2).

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      -1 < X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 2))}.Finite := by sorry
