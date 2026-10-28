-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_initial_record_trueExit_factor_lower
-- name    : AvramDividend.Classical.chat12_initial_record_trueExit_factor_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:14:01.443653+00:00
-- url     : https://prove2.me/theorems/05d6ec24-dfd3-4386-89cc-fb90544c6f89
-- title:
--   First surviving killed record dominates the strict two-sided-exit discount factor
-- statement:
--   Scale-free first-record lower expectation: epsilon times discounted strict upward exit before crossing epsilon-minus-a is bounded by the first surviving killed upward-record reward. It is a consequence of the proved pathwise strict-exit domination and nonnegative integral scaling and does not require a scale function or its exit-ratio identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_weight_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.chat12_initial_record_trueExit_factor_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ENNReal.ofReal ε *
      (∫⁻ ω, if twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by sorry
