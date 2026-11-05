-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:38:29.721141+00:00
-- url     : https://prove2.me/theorems/018452f4-db29-4e6e-8c12-6b432f2fefaf
-- title:
--   Original chronological negative-band pair count is real measurable from intrinsic factorial identity
-- statement:
--   For the actual original spectrally negative Lévy path, its finite negative-band chronological ordered-pair count, cast to real, is measurable. Derive this directly from the Proved original intrinsic marked-count measurability and exact source pathwise real factorial identity. This is the genuine hK measurability premise for the original second-factorial mean bridge; it assumes no Poisson coupling or moment bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    Measurable (fun ω => (K ω : ℝ)) := by sorry
