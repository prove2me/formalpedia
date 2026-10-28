-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_monotone
-- name    : AvramDividend.Classical.dividendStrategy_realTime_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:50:13.224996+00:00
-- url     : https://prove2.me/theorems/45fef7a6-a83f-4e4f-9d65-8f8ae1312332
-- title:
--   Real-time cumulative dividend paths are monotone for Stieltjes measure construction
-- statement:
--   A dividend strategy is nondecreasing in nonnegative time, and the clipping map t.toNNReal from real time to nonnegative time is nondecreasing. Their composition is therefore monotone on the entire real line. This is precisely the predicate tested in the dividendMeasure definition before constructing the Stieltjes measure.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_realTime_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Monotone (fun t : ℝ => D t.toNNReal ω) := by sorry
