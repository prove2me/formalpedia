-- Prove2me | solution 1 for stageB_shiftedSup_drawdown_clock_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T00:37:26.999944+00:00
-- url     : https://prove2.me/submissions/bad1e905-5712-4833-b9f6-911133fa4ccf

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_origin_sampled_reflected_reward_eq_true
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_sampled_reward_true_pair
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_two_record_discount_pathwise
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) (u : ℝ≥0) :
    (⨅ i : {t : ℝ≥0 // (X.X (u + t) ω - X.X u ω) -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) '' Icc 0 t) < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ i : {t : ℝ≥0 // X.X (u + t) ω -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
      (i.1 : ℝ≥0∞)) := by
  simp only [iInf_subtype]
  apply iInf_congr
  intro t
  have hbd : BddAbove ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) := by
    obtain ⟨v, hv⟩ := levyPath_bddAbove_Icc X ω (u + t)
    refine ⟨v, ?_⟩
    rintro z ⟨r, hr, rfl⟩
    exact hv ⟨u + r, ⟨zero_le, by
        calc
          u + r = r + u := add_comm u r
          _ ≤ t + u := add_le_add_left hr.2 u
          _ = u + t := add_comm t u⟩, rfl⟩
  have hx := shiftedSup_increment_eq_sup_sub (fun r => X.X r ω) u t hbd
  simp only [hx]
  have heq : ((X.X (u + t) ω - X.X u ω) -
        (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) - X.X u ω) < -a) ↔
      (X.X (u + t) ω -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a) := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  simp only [heq]
