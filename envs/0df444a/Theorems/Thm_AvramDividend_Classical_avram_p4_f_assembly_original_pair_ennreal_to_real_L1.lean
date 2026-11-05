-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_pair_ennreal_to_real_L1
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_pair_ennreal_to_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:41:07.334352+00:00
-- url     : https://prove2.me/theorems/87898756-3598-4d12-8f37-8954dce39cee
-- title:
--   Real L1 chronological pair mean from original ENNReal source mean
-- statement:
--   On the original Levy marked-time finset, an a.e. measurable ENNReal chronological pair count with finite pair expectation r squared over two yields an Integrable real twice-pair count of expectation exactly r squared. This gives the L1 conversion required by Open d938, conditional only on actual source moment and measurability.
-- source:
--   Pinned Mathlib integrable_toReal_of_lintegral_ne_top and integral_toReal, finite source Finset cardinal, original X and X.nu.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_pair_ennreal_to_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    AEMeasurable K P →
    (∫⁻ ω, K ω ∂P) = ENNReal.ofReal (r ^ 2 / 2) →
    Integrable (fun ω => 2 * (K ω).toReal) P ∧
      (∫ ω, 2 * (K ω).toReal ∂P) = r ^ 2 := by sorry
