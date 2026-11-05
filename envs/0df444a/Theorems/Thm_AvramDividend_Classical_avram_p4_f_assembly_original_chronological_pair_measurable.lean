-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_measurable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:51:51.362808+00:00
-- url     : https://prove2.me/theorems/de3b5f97-ea92-47cf-bfa3-bd0a9721b4c4
-- title:
--   Original negative-band chronological pair count is measurable
-- statement:
--   The actual original X negative-band chronological pair count, viewed as ENNReal, is globally measurable on Ω. Use P2-E original marked-rectangle count measurability and the accepted physical path factorial identity, with Nat→ENNReal a measurable embedding and countable-domain arithmetic.
-- source:
--   P2-E marked count measurable 5cb1e247, finite negative marked-time factorial pair identity 7cf25aa9, Mathlib MeasurableEmbedding.natCast and measurable_of_countable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    Measurable (fun ω : Ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)) := by sorry
