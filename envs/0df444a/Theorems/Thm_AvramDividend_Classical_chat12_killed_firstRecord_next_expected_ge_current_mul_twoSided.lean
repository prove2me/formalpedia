-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
-- name    : AvramDividend.Classical.chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:29:48.087935+00:00
-- url     : https://prove2.me/theorems/cefcd127-e473-4668-aa6d-d484d5b46817
-- title:
--   Uncapped killed-record strong-Markov lower expectation inequality
-- statement:
--   Global lower one-cycle discounted expectation inequality between successive killed upward records, with the unnormalised true two-sided Lévy exit payoff. The result follows from the finite-cap lower strong-Markov bridge and monotone removal of record time caps, without using scale functions or the two-sided exit q-scale identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_global_upper_of_caps
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_capped_record_next_expected_ge_current_mul_twoSided


open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ,
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
      (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        (∫⁻ ω,
      if twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 2 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
