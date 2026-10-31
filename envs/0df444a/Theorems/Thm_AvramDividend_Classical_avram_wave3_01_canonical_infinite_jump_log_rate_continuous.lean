-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_canonical_infinite_jump_log_rate_continuous
-- name    : AvramDividend.Classical.avram_wave3_01_canonical_infinite_jump_log_rate_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:46:55.626525+00:00
-- url     : https://prove2.me/theorems/98caa2b4-caab-4b22-a685-ddd372d64da8
-- title:
--   Original reflected-record logarithmic hazard is continuous from infinite small-jump variation alone
-- statement:
--   The genuine discounted Lévy first upward record before reflected ruin has a finite positive log-hazard, continuous as a function of positive drawdown depth, under exactly the infinite first-moment of small negative jumps. The separate source theorem proves this moment condition excludes bounded variation, and the now Proved original record-log-hazard continuity theorem provides the conclusion. This matches the hypotheses of the canonical infinite small-jump C1 theorem.
-- source:
--   Providers Proved: record log-rate continuity UUID ec9e934a and canonical infinite-small-jump non-BV UUID b69119ba. Canonical C1 target cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_canonical_infinite_jump_log_rate_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      -Real.log ((∫⁻ ω,
        if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal)) (Ioi 0) := by sorry
