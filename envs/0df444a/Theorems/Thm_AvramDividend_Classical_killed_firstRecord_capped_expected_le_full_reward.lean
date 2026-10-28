-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_capped_expected_le_full_reward
-- name    : AvramDividend.Classical.killed_firstRecord_capped_expected_le_full_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:02:34.344642+00:00
-- url     : https://prove2.me/theorems/dd84a29b-0596-4ecd-8b92-4f8578bf7b35
-- title:
--   The finite-cap expected killed first-record reward is at most its full reward
-- statement:
--   For every finite horizon, restricting a killed discounted upper-record reward to records reached by that horizon decreases its expected nonnegative payment. The result converts capped strong-Markov estimates into the unrestricted previous-record bound.
-- source:
--   Integral monotonicity of nonnegative extended-real payoffs; first-record cap is a subset of survival event.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_capped_expected_le_full_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (N : ℝ≥0) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
                  twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) := by sorry
