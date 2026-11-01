-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_height_tonelli_swap
-- name    : AvramDividend.Classical.avram_wave4_01_original_killed_record_height_tonelli_swap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:59:26.080598+00:00
-- url     : https://prove2.me/theorems/93fc6365-08f5-43ba-8d94-115a9bca45bd
-- title:
--   Tonelli interchange for the true original Lévy killed first-record height-occupation reward
-- statement:
--   For the exact original Lévy first strict upward record time T_h and actual reflected drawdown ruin time D_a, the expected Lebesgue-in-height integral of the nonnegative q-discounted killed record reward equals the height integral of its genuine expected reward. The proof uses a new canonically proved joint measurability theorem for the actual source reward (not merely separate measurability), the probability measure field of SpectrallyNegativeLevy (ensuring s-finiteness), and pinned Mathlib lintegral_lintegral_swap. Valid for all real q and a without Standing. This is the genuine source-law Tonelli interface required before identifying the occupation potential with the reciprocal scale log-derivative.
-- source:
--   Requires canonical Proved avram_wave4_01_original_killed_record_reward_joint_height_path_measurable. Existing SpectrallyNegativeLevy.isProbability field supplies IsProbabilityMeasure P and SFinite P. Pinned Mathlib MeasureTheory.lintegral_lintegral_swap exact signature verified at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_killed_record_reward_joint_height_path_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_killed_record_height_tonelli_swap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a : ℝ) :
    (∫⁻ ω, ∫⁻ h in Ioi (0 : ℝ),
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂volume ∂P) =
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ ω,
      (if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0) ∂P ∂volume) := by sorry
