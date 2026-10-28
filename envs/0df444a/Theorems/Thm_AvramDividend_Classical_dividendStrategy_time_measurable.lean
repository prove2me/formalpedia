-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_time_measurable
-- name    : AvramDividend.Classical.dividendStrategy_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:43:17.05698+00:00
-- url     : https://prove2.me/theorems/9816592b-d69d-42e0-afbe-697da6150cbc
-- title:
--   Cumulative dividend paths are measurable in time
-- statement:
--   Every dividend strategy has a nondecreasing cumulative dividend path as part of its IsDividendStrategy definition. The path is therefore Borel measurable in time, independently of right-jump sizes. This is a precise measurable-path prerequisite for the controlled reserve and Stieltjes stopping arguments.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_time_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ≥0 => D t ω) := by sorry
