-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_count_centered_L2_of_pair_mean_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_count_centered_L2_of_pair_mean_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:33:16.396019+00:00
-- url     : https://prove2.me/theorems/dd11f686-0aa1-4d22-82a5-7f753ce43ba0
-- title:
--   Original centred negative-band marked count has L2 and variance from pair moment alone
-- statement:
--   For actual source Lévy negative-band marked jumps, the first-moment L1 and exact real source ν-rate are now automatic. Once genuinely separate chronological source pair integrability and its exact moment have been established, the existing centred-count variance interface gives L2 and variance r. This statement imports no Poisson variables or extra first moment hypotheses and isolates the sole pair mean proof obligation.
-- source:
--   Proved 7e452475 original centered L2 conditional; 3d8bb7f8 original L1; c1e09ada original real mean (publication/proof pending before writing).

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_centered_count_l2_pair_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_count_centered_L2_of_pair_mean_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P →
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 →
    Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by sorry
