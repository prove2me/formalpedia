-- Prove2me | solution 1 for stageB_ndd_iff_rat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T01:14:52.143145+00:00
-- url     : https://prove2.me/submissions/b25dee24-37ed-4d7f-9747-6a367dbd7d0b

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
import Theorems.Thm_stageB_tauPlus_lt_iff
import Theorems.Thm_stageB_reflect_eq
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (ω : Ω)
    (hfin : twoSidedExitUpTime X b ω ≠ ⊤) :
    NoDrawdownBeforeUpcrossing X.X b h ω ↔ ∃ r : stageB_Bars h, stageB_bpay X (r : ℝ) b 0 ω ≠ 0 := by
  let U := twoSidedExitUpTime X b ω
  let u : ℝ≥0 := U.toNNReal
  have huU : (u : ℝ≥0∞) = U := ENNReal.coe_toNNReal hfin
  have huClock : (u : ℝ≥0∞) = ⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞) := by simpa [U, twoSidedExitUpTime] using huU
  constructor
  · intro hnd
    obtain ⟨v, hvI, hvmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
      (⟨0, ⟨le_rfl, bot_le⟩⟩ : (Icc (0 : ℝ≥0) u).Nonempty) isCompact_Icc (reflectedSup_upperSemicontinuousOn_Icc X ω u)
    have hdv : reflectedSup X v ω < h := by
      by_cases hvlt : v < u
      · have ht : (v : WithTop ℝ≥0) < tauPlus X.X b ω := (stageB_tauPlus_lt_iff X b ω (t := v)).2 (by simpa only [huU] using (ENNReal.coe_lt_coe.mpr hvlt))
        simpa only [stageB_reflect_eq X v ω] using hnd v ht
      · have hvu : v = u := le_antisymm hvI.2 (le_of_not_gt hvlt)
        have hz := firstUpcrossing_runningSup_sub_path_eq_zero X b (le_of_lt hb) ω u huClock
        have hz_lt : runningSup X u ω - X.X u ω < h := by
          rw [hz]
          exact hh
        simpa only [hvu, reflectedSup] using hz_lt
    have hm : max 0 (reflectedSup X v ω) < h := max_lt hh hdv
    obtain ⟨q, hq0, hqh⟩ := exists_rat_btwn hm
    let r : stageB_Bars h := ⟨q, ⟨lt_of_le_of_lt (le_max_left _ _) hq0, hqh⟩⟩
    refine ⟨r, ?_⟩
    have hbefore : ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ (q : ℝ) := by
      intro t ht
      exact le_trans (hvmax ⟨bot_le, le_of_lt ht⟩) (le_trans (le_max_right _ _) hq0.le)
    have hru := firstUpcrossing_strictly_before_drawdown_ruin X (q : ℝ) b (lt_of_le_of_lt (le_max_left _ _) hq0) (le_of_lt hb) ω u huClock hbefore
    have hru' : U < barrierRuinTime X (q : ℝ) ω := by simpa only [barrierRuinTime, drawdown, huU] using hru
    have hrU : twoSidedExitUpTime X b ω < barrierRuinTime X (q : ℝ) ω := by simpa only [U] using hru'
    simp [stageB_bpay, r, hrU]
  · rintro ⟨r, hr⟩
    have hrU : U < barrierRuinTime X (r : ℝ) ω := by
      have hcond : twoSidedExitUpTime X b ω < barrierRuinTime X (r : ℝ) ω := by
        by_contra hc
        simp [stageB_bpay, hc] at hr
      simpa only [U] using hcond
    have hru : (u : ℝ≥0∞) < barrierRuinTime X (r : ℝ) ω := by simpa only [huU] using hrU
    have hsurv := (firstUpcrossing_before_barrierRuin_iff_prefix_survival X (r : ℝ) b r.2.1 (le_of_lt hb) ω u huClock).mp hru
    intro t ht
    have htU : (t : ℝ≥0∞) < U := (stageB_tauPlus_lt_iff X b ω (t := t)).1 ht
    have ht' : t < u := ENNReal.coe_lt_coe.mp (by simpa only [huU] using htU)
    simpa only [stageB_reflect_eq X t ω] using lt_of_le_of_lt (hsurv t ht') r.2.2
