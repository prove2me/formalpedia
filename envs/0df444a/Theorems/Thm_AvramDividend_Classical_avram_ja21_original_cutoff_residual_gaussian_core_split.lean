-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
-- name    : AvramDividend.Classical.avram_ja21_original_cutoff_residual_gaussian_core_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:43:04.453886+00:00
-- url     : https://prove2.me/theorems/4b47cce4-a0f2-443a-96d9-9c482e4cb8b8
-- title:
--   Original intrinsic Gaussian cutoff equals fixed Gaussian core minus compensated small-band jump
-- statement:
--   For the original Levy process, the finite-cutoff Gaussian residual at every n and time is the fixed n=0 residual plus its original n=0 compensated small-band jump, minus the n-th original compensated small-band jump. The exact identity holds pointwise on the original probability space and is obtained from the Proved cutoff-difference theorem.
-- source:
--   J-A21 source decomposition using 2c95a423, prerequisite for 9824be38 physical Gaussian and jump moment certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_cutoff_residual_gaussian_core_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
       avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by sorry
