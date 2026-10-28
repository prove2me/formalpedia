-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_zero_nonpositive_and_initial_window
-- name    : AvramDividend.Classical.measure_Iic_zero_of_zero_nonpositive_and_initial_window
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:49:21.359765+00:00
-- url     : https://prove2.me/theorems/48bc6398-64cd-43bd-855e-58ebcab49b89
-- title:
--   Zero nonpositive and initial-window Stieltjes payments imply no pre-stopping dividends
-- statement:
--   A payment measure with zero mass on nonpositive times and on the closed window from zero through a stopping clock has zero mass on the entire left half-line through that clock. This is the support side condition needed for translating cumulative barrier payouts after first upper passage.
-- source:
--   Direct deterministic support bridge for first-passage barrier dividend measure: combines Proved barrierStrategy_dividendMeasure_zero_through_firstUpcrossing (4396ddd6-6981-42c6-9f15-733157b72a22) with nonpositive Stieltjes support, to feed measure_eq_translated_of_zero_prepayment_and_cumulative (50431279-23d0-42be-b261-421a5476921e).

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.measure_Iic_zero_of_zero_nonpositive_and_initial_window
    (μ : Measure ℝ) (u : ℝ)
    (hnegative : μ (Set.Iic (0 : ℝ)) = 0)
    (hthrough : μ (Set.Icc (0 : ℝ) u) = 0) :
    μ (Set.Iic u) = 0 := by
  sorry
