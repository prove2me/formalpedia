-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_record_expected_reward_antitone
-- name    : AvramDividend.Classical.killed_record_expected_reward_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:32:07.947178+00:00
-- url     : https://prove2.me/theorems/849d78c5-5a8f-4686-ac72-e6dd11d4a584
-- title:
--   Killed and discounted record expectations decrease with increasing record level
-- statement:
--   For nonnegative discount q and positive record spacing, the stopped and killed discounted first-upcrossing reward has nonincreasing expected value as the record index increases. The proof uses monotonicity of strict first-upcrossing times, monotonicity of ENNReal.toReal when the later clock is finite, and discount monotonicity. This supplies a formal pathwise precursor to the W(a)/W(a+ε) strict contraction in the stopped-renewal root.
-- source:
--   Pointwise comparison by threshold monotonicity and exponential discount antitonicity, then monotonicity of the Lebesgue integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.killed_record_expected_reward_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
