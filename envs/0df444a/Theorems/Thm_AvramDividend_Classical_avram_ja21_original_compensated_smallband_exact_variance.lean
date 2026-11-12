-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_compensated_smallband_exact_variance
-- name    : AvramDividend.Classical.avram_ja21_original_compensated_smallband_exact_variance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T14:49:48.50917+00:00
-- url     : https://prove2.me/theorems/d73cacfa-0d1c-469a-a411-19f0a3fa81be
-- title:
--   Original physical compensated small-jump finite cutoff has exact Lévy-band variance
-- statement:
--   Prove the exact L2 variance of the n-th physical original compensated small-band jump sum, using existing original finite marked count isometry, without large-mark first moments.
-- source:
--   J-A21 atomic source-moment reduction of 10ff2b5a, supported by Proved source identity 4b47cce4, measurability f7cf0440 and jump L2 envelope c64684fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_compensated_smallband_exact_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
