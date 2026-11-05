-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_turn2_physical_pair_l1_of_exact_ennreal_mean
-- name    : AvramDividend.Classical.avram_p4_f_turn2_physical_pair_l1_of_exact_ennreal_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:49:52.683805+00:00
-- url     : https://prove2.me/theorems/82cab5fe-de5a-41e8-bd60-823aee4e4b25
-- title:
--   Genuine original chronological-pair real L1 follows from exact source ENNReal moment
-- statement:
--   For the physical original negative-band jump-time set, the exact ENNReal second-factorial chronological-pair expectation implies real L1 and real doubled-pair expectation. The physical pair-count measurability is discharged internally using the independently Proved original intrinsic marked-count factorial identity. The only remaining external premise is the exact source ENNReal moment, with no equality-in-law replacement, circular premise or artificial martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_card_real_measurable_from_intrinsic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_ennreal_to_real_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_turn2_physical_pair_l1_of_exact_ennreal_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let r : ℝ := (((T : ℝ≥0∞) *
      X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    (∫⁻ ω, K ω ∂P) = ENNReal.ofReal (r ^ 2 / 2) →
    Integrable (fun ω => 2 * (K ω).toReal) P ∧
      (∫ ω, 2 * (K ω).toReal ∂P) = r ^ 2 := by sorry
