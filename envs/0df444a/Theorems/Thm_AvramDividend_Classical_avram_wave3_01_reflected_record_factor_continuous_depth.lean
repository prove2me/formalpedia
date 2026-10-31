-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_factor_continuous_depth
-- name    : AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:30:40.657395+00:00
-- url     : https://prove2.me/theorems/700e39bd-5adb-4dfe-9ca0-f5796d645f14
-- title:
--   Actual pure-jump discounted reflected first-record survival is continuous in killing depth
-- statement:
--   For a genuine original spectrally negative Lévy process with infinite small-jump variation, the discounted expectation of an upward first record at b before strict reflected ruin is continuous as a function of the positive reflected drawdown threshold. The exact source finite-record reflected maximum has no positive atoms, and pathwise survival equals its closed threshold bound; the original killed discount is measurable and bounded by one, so finite-probability nonnegative dominated convergence applies. All results use source first-passage clocks without Standing assumptions or conditional C1 assumptions.
-- source:
--   Original-Lévy first-record atomlessness 35f216f9; source prefix survival 9a4b2916, record reflected zero 9243feef, upper-semicontinuity 8cec706c; measurable killed discount cd7b1f13; pinned Mathlib DCT; source SpectrallyNegativeLevy probability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_first_record_height_atomless
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a c : ℝ≥0, a < c →
      ∃ m : ℕ, a < times m ∧ times m < c)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) (Ioi 0) := by sorry
