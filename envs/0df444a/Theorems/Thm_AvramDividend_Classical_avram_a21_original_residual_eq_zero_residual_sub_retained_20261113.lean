-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
-- name    : AvramDividend.Classical.avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:56:00.437293+00:00
-- url     : https://prove2.me/theorems/bfc8537f-0cb7-46eb-a7d0-8f0f3dab3d09
-- title:
--   Original intrinsic residual equals zero-cutoff residual minus retained compensated physical jump strip
-- statement:
--   For any original spectrally negative Lévy process, time, sample and cutoff, the physical intrinsic residual equals the zero-cutoff residual less the retained compensated negative small-jump band, with exact source sign and mark endpoints.
-- source:
--   Proved original cutoff residual split 4b47cce4 and zero retained-band compensator 8d8eedb1; avoids re-expanding original process definitions and is the key algebraic bridge to original finite-cutoff Gaussian moment 74450e6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by sorry
