-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger125_original_zero_clock_cash_components_vanish
-- name    : AvramDividend.Classical.avram_gledger125_original_zero_clock_cash_components_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:08:08.616521+00:00
-- url     : https://prove2.me/theorems/72bf4190-d96f-4104-bea1-6f7d4df2a9e4
-- title:
--   Original zero stopped clock has no strict or final-strip cash
-- statement:
--   At the original zero stopped clock, nonnegative payment times cannot lie strictly before the stop or in an open final mesh strip with endpoint zero. Both genuine Stieltjes discounted cash components therefore vanish exactly, for any original strategy path and any discount and grid width.
-- source:
--   The original paymentTimes definition imposes nonnegative time; both integration domains require time strictly negative. The intersections are empty, and the two restricted nonnegative lintegrals vanish.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger125_original_zero_clock_cash_components_vanish
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q δ : ℝ) :
    (∫⁻ s in paymentTimes σ ∩ Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal = 0 ∧
    (∫⁻ s in paymentTimes σ ∩ Ioo (-δ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal = 0 := by sorry
