-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment
-- name    : AvramDividend.Classical.dividendMeasure_Ico_eq_dividend_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:15:25.570999+00:00
-- url     : https://prove2.me/theorems/fad162c7-51f3-4381-8de7-96e01634c5c8
-- title:
--   The dividend Stieltjes measure of every nonnegative half-open interval equals the dividend path increment
-- statement:
--   For any strategy D, path ω and any two nonnegative times a,b, the exact mission dividendMeasure mass on the real half-open interval [a,b) equals ENNReal.ofReal(D_b−D_a). When a>b both sides are zero by monotonicity. The measure is the Stieltjes measure of the right-continuous real extension of a left-continuous dividend process, so it correctly includes continuously accumulated dividends and right jumps. This generalises the previous [0,t) special case and supports interval-by-interval estimates of the full discounted dividend integral.
-- source:
--   Child monotone_leftcontinuous_stieltjes_measure_Ico, dividendStrategy_real_extension_leftContinuous; exact dividendMeasure model definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ico_eq_dividend_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - D a ω) := by sorry
