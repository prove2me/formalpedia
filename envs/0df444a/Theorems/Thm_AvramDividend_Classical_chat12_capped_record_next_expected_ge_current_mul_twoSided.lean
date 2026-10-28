-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_capped_record_next_expected_ge_current_mul_twoSided
-- name    : AvramDividend.Classical.chat12_capped_record_next_expected_ge_current_mul_twoSided
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:27:57.414703+00:00
-- url     : https://prove2.me/theorems/675e6c7a-af8d-4630-9911-2613c19d621e
-- title:
--   Finite-horizon strong-Markov lower expectation for consecutive surviving killed records
-- statement:
--   For a spectrally negative Levy path, the genuine discounted two-sided exit expectation with upper increment epsilon and lower increment epsilon-minus-a, multiplied by the finite-horizon surviving first-record discounted reward, is bounded above by the full expected surviving next-record reward. This is the standalone stochastic lower-renewal bridge without any scale-function assumptions; a capped stopping time, pathwise lower domination and the strong-Markov expectation theorem establish the bound.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_finiteStopping_trueTwoSided_expected_lower_imported
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_true_clock_within_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_weight_ge_countable_twoSided_reward

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_capped_record_next_expected_ge_current_mul_twoSided
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε)
    (N : ℝ≥0) :
    (∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
      twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) := by sorry
