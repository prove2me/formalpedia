-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_record_discount_antitone_level
-- name    : AvramDividend.Classical.avram_wave3_01_record_discount_antitone_level
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:18:27.226807+00:00
-- url     : https://prove2.me/theorems/7bd9562c-1e76-4452-aa69-25b37ef5c0fe
-- title:
--   Monotonicity of the genuine killed discounted upward first-record factor in record height
-- statement:
--   For the original spectrally negative Lévy process, at fixed positive reflected ruin barrier and positive discount, the nonnegative discounted expectation of reaching an upper level before reflected ruin decreases as the upper record level increases. This uses monotonicity of the actual first-upcrossing clock, strict survival event inclusion and monotonicity of the exponential discount, including infinite first-passage times.
-- source:
--   Canonical Proved twoSidedExitUpTime_mono_threshold 5060f2c9; source definitions of reflected strict ruin and discounted killed first record.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_record_discount_antitone_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q b c : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0 ∂P) := by sorry
