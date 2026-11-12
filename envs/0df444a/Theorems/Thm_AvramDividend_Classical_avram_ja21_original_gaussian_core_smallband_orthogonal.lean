-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_smallband_orthogonal
-- name    : AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_orthogonal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T14:49:52.812173+00:00
-- url     : https://prove2.me/theorems/1e8c653a-e252-4f04-ac04-d09c7f83f407
-- title:
--   Original Gaussian core is orthogonal to compensated physical small-band jump at every cutoff
-- statement:
--   Prove zero covariance between the fixed physical Gaussian core R0+Jsmall0 and the negative n-th compensated small-jump cutoff, all on the original probability space and original filtration.
-- source:
--   J-A21 atomic source-moment reduction of 10ff2b5a, supported by Proved source identity 4b47cce4, measurability f7cf0440 and jump L2 envelope c64684fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) * (-(avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)) ∂P) = 0 := by sorry
