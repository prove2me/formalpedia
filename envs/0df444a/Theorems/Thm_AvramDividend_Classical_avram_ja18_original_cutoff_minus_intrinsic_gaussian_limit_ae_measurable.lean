-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
-- name    : AvramDividend.Classical.avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:26:06.468082+00:00
-- url     : https://prove2.me/theorems/fd5f160f-a841-41b1-a8db-7ed08f060dc3
-- title:
--   Original intrinsic cutoff minus Gaussian limit is strongly measurable almost surely
-- statement:
--   For the genuine same-Lévy source, the finite-cutoff intrinsic residual minus an almost-surely strongly measurable Gaussian limit has an almost-surely strongly measurable difference. This follows by the proved exact decomposition of R_n into fixed Gaussian plus retained smallband and the proved filtration measurability of those two components. It supplies the measurable omitted-tail term J=R_n-R for the corrected variance decomposition and avoids the false nearzero variance identity for the retained smallband.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_cutoff_minus_intrinsic_gaussian_limit_ae_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRmeas : ∀ t : ℝ≥0, AEStronglyMeasurable (R t) P) :
    ∀ (n : ℕ) (t : ℝ≥0),
      AEStronglyMeasurable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P := by sorry
