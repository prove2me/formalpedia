-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_fixed_gaussian_core_second_moment
-- name    : AvramDividend.Classical.avram_ja21_original_fixed_gaussian_core_second_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T14:49:53.877838+00:00
-- url     : https://prove2.me/theorems/b12c5163-0ad7-41c8-9a34-6d6a88f6bca1
-- title:
--   Original original-space cutoff-independent Gaussian core is L2 with exact sigma-square variance
-- statement:
--   Prove the physical original-space Gaussian core R0+Jsmall0 is square-integrable and has exact variance t sigma squared. No auxiliary Brownian identification.
-- source:
--   J-A21 atomic source-moment reduction of 10ff2b5a, supported by Proved source identity 4b47cce4, measurability f7cf0440 and jump L2 envelope c64684fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_fixed_gaussian_core_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by sorry
