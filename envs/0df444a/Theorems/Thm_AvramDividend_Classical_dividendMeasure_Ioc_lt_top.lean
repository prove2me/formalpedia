-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_lt_top
-- name    : AvramDividend.Classical.dividendMeasure_Ioc_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:22:48.55699+00:00
-- url     : https://prove2.me/theorems/28a30b86-b88f-4450-80d8-35c09c0a44e8
-- title:
--   Every fixed bounded interval has finite Stieltjes dividend mass for an adapted nondecreasing strategy
-- statement:
--   The dividend Stieltjes measure of any adapted, left-continuous, nondecreasing real-valued cumulative dividend strategy has finite mass on each bounded half-open real interval. The measure is the Stieltjes measure of the real-time monotone extension D(t.toNNReal), whose interval mass is the extended-nonnegative positive part of the finite difference between two values of its Stieltjes function. This supplies the pointwise-finite interval pieces needed to construct a general s-finite random dividend kernel, extending the already proved running-supremum special case.
-- source:
--   Mathlib.MeasureTheory.Measure.Stieltjes; StieltjesFunction.measure_Ioc; Monotone.stieltjesFunction_eq; definition of dividendMeasure.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ioc_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ) :
    dividendMeasure D ω (Ioc a b) < ⊤ := by sorry
