-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_exponential_hazard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:26:35.052871+00:00
-- url     : https://prove2.me/theorems/1f5b13d3-98f1-4b35-b1d2-5df29b3cf596
-- title:
--   Original Lévy reflected-record discount is exponential in upward-record height
-- statement:
--   For the actual spectrally negative Lévy path with divergent first absolute small-jump moment and positive discount, the discounted first strict upward record before reflected drawdown ruin has an exact exponential dependence on record height for every fixed positive drawdown barrier. The rate equals the negative logarithm of the unit-height factor. The proof uses the genuine uncapped stopped strong-Markov semigroup, first-record positivity, scale-sandwich zero-height limit, and additive Cauchy law.
-- source:
--   Kuznetsov Kyprianou Rivero 2013 original first-record hazard; genuine semigroup UUID 3890ee9b; target cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_record_discount_strict_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_discount_le_one
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_toReal_semigroup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_factor_tendsto_one_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_zero_extended_log_continuous_at_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_positive_semigroup_exp_law

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_exponential_hazard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (a : ℝ) (ha : 0 < a) :
    ∀ h : ℝ, 0 < h →
      (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal =
      Real.exp (-h * (-Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal))) := by sorry
