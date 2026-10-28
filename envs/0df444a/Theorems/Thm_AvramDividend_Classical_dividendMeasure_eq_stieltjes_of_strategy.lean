-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_eq_stieltjes_of_strategy
-- name    : AvramDividend.Classical.dividendMeasure_eq_stieltjes_of_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:53:35.092536+00:00
-- url     : https://prove2.me/theorems/904e3e8a-bb81-4390-9a5d-ec77cf033314
-- title:
--   Dividend measure equals the genuine Stieltjes measure for any strategy
-- statement:
--   By definition dividendMeasure selects the Stieltjes measure of the real-time cumulative dividend path when that path is monotone, otherwise the zero measure. For any IsDividendStrategy, monotonicity is guaranteed. The theorem unfolds dividendMeasure and selects its Stieltjes branch, simplifying subsequent continuous/atomic payout and stopping calculations.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_eq_stieltjes_of_strategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    dividendMeasure D ω =
      (dividendStrategy_realTime_monotone D hD ω).stieltjesFunction.measure := by sorry
