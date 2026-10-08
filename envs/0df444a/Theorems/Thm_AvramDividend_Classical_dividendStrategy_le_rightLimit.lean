-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
-- name    : AvramDividend.Classical.dividendStrategy_le_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:01:07.545329+00:00
-- url     : https://prove2.me/theorems/953f0e91-72ae-4c9a-bc17-de52a6c87b52
-- title:
--   A monotone dividend path is below its strict-right limit
-- statement:
--   For a nondecreasing dividend path, the current cumulative dividend is a lower bound for all later values and therefore for their infimum, the strict-right limit.
-- source:
--   Elementary helper for the jump term in Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_le_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    D t ω ≤ rightLimit D t ω := by sorry
