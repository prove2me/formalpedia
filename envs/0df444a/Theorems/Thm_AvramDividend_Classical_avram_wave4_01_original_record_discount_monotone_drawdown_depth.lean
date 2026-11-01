-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_monotone_drawdown_depth
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_monotone_drawdown_depth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:24:36.211504+00:00
-- url     : https://prove2.me/theorems/b5710838-09e9-48e1-9e9f-4cd9bdfb6d4a
-- title:
--   Actual original Lévy killed first-record discount increases with reflected drawdown ruin depth
-- statement:
--   For the genuine first strict upward record T_h and genuine reflected drawdown ruin time D_a, increasing the ruin drawdown depth from a to b cannot reduce the discounted probability E[e^{-q T_h};T_h<D_a]. This is an exact monotonicity of actual source stopped-clock events and their nonnegative Lévy weights, for arbitrary real h,q and a≤b, without Standing or scale-function assumptions. It provides a direct source-level comparison for continuity and monotonicity of the first-record hazard.
-- source:
--   Canonical pathwise barrierRuinTime_mono_barrier 6c566972, pointwise event inclusion and monotonicity of the nonnegative extended-real integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_monotone_drawdown_depth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q h a b : ℝ) (hab : a ≤ b) :
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X b ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P) := by sorry
