-- Prove2me | solution 1 for stageB_actual_height_barrier_semigroup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T00:20:26.313973+00:00
-- url     : https://prove2.me/submissions/947ee5a8-e39f-4409-b383-dc5d514a38a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_shiftedSup_drawdown_clock_eq
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
    (X : SpectrallyNegativeLevy P 𝓕) (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal))) else 0 ∂P) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    let ρ : ℝ≥0∞ := ⨅ i : ℕ, if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
    let σ : ℝ≥0∞ := ⨅ i : ℕ, if f (samples i) - f 0 - (⨆ j : ℕ, if samples j ≤ samples i then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a then (samples i : ℝ≥0∞) else ⊤
    if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0
  let discount : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  have hr : Measurable reward := by simpa only [reward] using avram_wave3_01_fresh_reflected_reward_measurable samples a c q
  have hd : Measurable discount := by dsimp only [discount]; fun_prop
  have hOrig (ω : Ω) : reward (fun t => X.X t ω) = stageB_bpay X a c q ω := by
    simpa only [reward, samples, stageB_bpay] using avram_wave3_01_origin_sampled_reflected_reward_eq_true X a c q ω
  have hDclock (ω : Ω) (u : ℝ≥0) := stageB_shiftedSup_drawdown_clock_eq X a ω u
  have hFuture (ω : Ω) (u : ℝ≥0) : reward (fun t => X.X (u + t) ω - X.X u ω) =
      (let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)
       let D : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // X.X (u + t) ω - sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞)
       if U < D then ENNReal.ofReal (Real.exp (-(q * U.toReal))) else 0) := by
    have hh := avram_wave3_01_shifted_sampled_reward_true_pair X a c q ω u
    simpa [reward, samples, hDclock ω u] using hh
  have hPath (ω : Ω) :
      (if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0) =
      (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then discount ((twoSidedExitUpTime X b ω).toNNReal) * reward (fun t => X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω - X.X ((twoSidedExitUpTime X b ω).toNNReal) ω) else 0) := by
    have hh := avram_wave3_01_two_record_discount_pathwise X a b c q ha hb hc ω
    simpa only [discount, ← hFuture] using hh
  have hFactor := avram_wave3_01_uncapped_reflected_killed_future_reward_factor X a b discount hd reward hr
  dsimp only at hFactor
  calc
    _ = (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then discount ((twoSidedExitUpTime X b ω).toNNReal) * reward (fun t => X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω - X.X ((twoSidedExitUpTime X b ω).toNNReal) ω) else 0 ∂P) := lintegral_congr hPath
    _ = (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then discount ((twoSidedExitUpTime X b ω).toNNReal) else 0 ∂P) * (∫⁻ ω, reward (fun t => X.X t ω) ∂P) := hFactor
    _ = _ := by
      refine congrArg₂ (· * ·) ?_ ?_
      · apply lintegral_congr
        intro ω
        exact congrArg (fun z : ℝ≥0∞ => if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then z else 0) (by simp only [discount, ENNReal.coe_toNNReal_eq_toReal])
      · exact lintegral_congr hOrig
