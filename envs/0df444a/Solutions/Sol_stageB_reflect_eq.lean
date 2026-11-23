-- Prove2me | solution 1 for stageB_reflect_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T00:48:52.925841+00:00
-- url     : https://prove2.me/submissions/1c283257-0265-4131-8a85-caf67f542fcc

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
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : reflectAtSup X.X 0 t ω = reflectedSup X t ω := by
  let S : Set ℝ := (fun u : ℝ≥0 => X.X u ω) '' Icc 0 t
  have hbd : BddAbove S := by simpa only [S] using levyPath_bddAbove_Icc X ω t
  have hbd' : BddAbove (Set.range fun s : Icc (0 : ℝ≥0) t => X.X s.1 ω) := by
    rcases hbd with ⟨M, hM⟩
    exact ⟨M, by rintro y ⟨s, rfl⟩; exact hM ⟨s.1, s.2, rfl⟩⟩
  obtain ⟨s0, hs0⟩ := (Set.nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ t))
  letI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨s0, hs0⟩⟩
  have hne : S.Nonempty := ⟨X.X s0 ω, ⟨s0, hs0, rfl⟩⟩
  have hsupi : (⨆ s : Icc (0 : ℝ≥0) t, X.X s.1 ω) = sSup S := by
    apply le_antisymm
    · exact ciSup_le (fun s => le_csSup hbd ⟨s.1, s.2, rfl⟩)
    · apply csSup_le hne
      rintro y ⟨u, hu, rfl⟩
      exact le_ciSup_of_le hbd' ⟨u, hu⟩ le_rfl
  have hnonneg : 0 ≤ sSup S := by
    apply le_csSup hbd
    exact ⟨0, ⟨le_rfl, bot_le⟩, by simpa [X.X_zero]⟩
  have hset : {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X.X u ω} = S := by
    ext y; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, ⟨bot_le, hu⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu.2, rfl⟩
  unfold reflectAtSup reflectedSup
  rw [Kyprianou.Ch08.runningSup, hset, (runningSup_eq_rawSup_nonneg X t ω).1, hsupi, max_eq_right hnonneg]
