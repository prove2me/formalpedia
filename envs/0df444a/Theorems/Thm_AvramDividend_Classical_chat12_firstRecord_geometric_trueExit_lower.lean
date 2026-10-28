-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueExit_lower
-- name    : AvramDividend.Classical.chat12_firstRecord_geometric_trueExit_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:31:35.080008+00:00
-- url     : https://prove2.me/theorems/b86c173f-5979-4cc1-b11c-84859029772c
-- title:
--   Scale-free geometric lower expected killed records from true two-sided exit
-- statement:
--   For each n, the (n+1)st surviving killed upward record has discounted expectation at least epsilon times the (n+1)st power of the genuine discounted strict two-sided-exit expectation. This combines the scale-free initial record lower bound with the already Proved uncapped one-cycle lower Markov recurrence and induction. No q-scale-function identity is used.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_next_expected_ge_current_mul_twoSided

import Theorems.Thm_AvramDividend_Classical_chat12_initial_record_trueExit_factor_lower
import Theorems.Thm_AvramDividend_Classical_chat12_firstRecord_geometric_trueFactor_of_base

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_firstRecord_geometric_trueExit_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ n : ℕ, ENNReal.ofReal ε * (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ^ (n + 1) ≤
      (∫⁻ ω, if twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((((n + 1 : ℕ)) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
