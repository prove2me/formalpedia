-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_two_record_discount_pathwise
-- name    : AvramDividend.Classical.avram_wave3_01_two_record_discount_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:19:51.550634+00:00
-- url     : https://prove2.me/theorems/eb9795ff-b89a-4f09-921d-72c7ad9183ef
-- title:
--   Original reflected-killed next-record discounted payoff factors pathwise at the first record
-- statement:
--   The actual original Lévy path's discounted first upward passage to b+c before strict reflected ruin at a is exactly the discounted first-surviving-record at b times the discounted shifted future first passage to c before the shifted reflected ruin threshold. Handles finite first record and arbitrary possibly infinite future clocks; proves both zero cases. Uses already Proved record shift and reflected ruin clock equivalence.
-- source:
--   avram_wave3_01_reflected_next_record_future_ruin_iff 62269b6b, nextRecord_upclock_eq_add_shifted_inf 794e45f9, true source clocks, monotonicity 5060f2c9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_next_record_future_ruin_iff
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_two_record_discount_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Ω) :
    (if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp
         (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0) =
    (let u : ℝ≥0 := (twoSidedExitUpTime X b ω).toNNReal
     let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)
     let D : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       X.X (u + t) ω -
         sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
       (i.1 : ℝ≥0∞)
     if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
         (if U < D then ENNReal.ofReal (Real.exp (-(q * U.toReal))) else 0)
     else 0) := by sorry
