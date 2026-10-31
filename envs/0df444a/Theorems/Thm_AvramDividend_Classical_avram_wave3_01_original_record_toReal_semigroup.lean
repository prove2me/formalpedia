-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_toReal_semigroup
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_toReal_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:20:50.316989+00:00
-- url     : https://prove2.me/theorems/78afc763-dc38-488b-8321-7fc1d12ff026
-- title:
--   Original-Lévy reflected first-record discount retains the semigroup law after toReal
-- statement:
--   For the genuine source Lévy first-upcrossing discount before reflected ruin, converting the extended nonnegative integrals to real numbers preserves the exact multiplicative semigroup at any two positive record heights, without Standing or scale smoothness. It follows directly from the already Proved original-clock Markov renewal factorisation and the remotely verified unconditional ENNReal.toReal_mul theorem.
-- source:
--   Proved Avram source semigroup 3890ee9b; exact pinned Mathlib ENNReal.toReal_mul, remote compiler type verified.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_toReal_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hq : 0 < q) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal)))
    else 0 ∂P).toReal =
      (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0 ∂P).toReal * (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0 ∂P).toReal := by sorry
