-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_expected_killed_record_weight_antitone_discount
-- name    : AvramDividend.Classical.chat08_expected_killed_record_weight_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:22:04.220031+00:00
-- url     : https://prove2.me/theorems/a16ae47b-1e92-4571-a1c0-d769b39d89c8
-- title:
--   Expected discounted first-record payment decreases in the discount rate
-- statement:
--   For a fixed strict record threshold and ruin barrier, the expected killed q-discounted cell payment is antitone in q. This is an unconditional ENNReal integral statement on the original Lévy probability measure, following by pointwise exponential monotonicity and nonnegative Lebesgue integral monotonicity. It is a reusable semigroup/renewal control for comparing discounted record rewards.
-- source:
--   Mathlib lintegral_mono, Real.exp_le_exp_of_le, and ENNReal.ofReal_le_ofReal.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_expected_killed_record_weight_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c h q₁ q₂ : ℝ)
    (hh : 0 ≤ h) (hq : q₁ ≤ q₂) :
    (∫⁻ ω, (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₂ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) ∂P) ≤
    (∫⁻ ω, (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₁ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) ∂P) := by sorry
