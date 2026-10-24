-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_killed_record_weight_antitone_discount
-- name    : AvramDividend.Classical.chat08_killed_record_weight_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:17:37.26701+00:00
-- url     : https://prove2.me/theorems/ea29e94d-f8ec-4adb-826a-4b6a049b227a
-- title:
--   Stopped first-record payments decrease as the discount rate rises
-- statement:
--   For any fixed strict upcrossing threshold, ruin barrier, path and nonnegative cell height, the killed exponential first-record payment is pointwise antitone in the nonnegative or arbitrary real discount rate. This follows from the nonnegative first-passage clock and monotonicity of the real exponential and of ENNReal.ofReal. It provides the discount-order comparison for future passage-law and renewal estimates.
-- source:
--   Mathlib Real.exp_le_exp_of_le and ENNReal.ofReal order preservation; official reflected ruin and upper passage times.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_killed_record_weight_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c h q₁ q₂ : ℝ)
    (hh : 0 ≤ h) (hq : q₁ ≤ q₂) (ω : Ω) :
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₂ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) ≤
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₁ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) := by sorry
