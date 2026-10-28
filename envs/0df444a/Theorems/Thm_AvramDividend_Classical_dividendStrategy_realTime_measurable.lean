-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_realTime_measurable
-- name    : AvramDividend.Classical.dividendStrategy_realTime_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:45:35.93085+00:00
-- url     : https://prove2.me/theorems/c763a94a-e6ba-4de3-a36f-f4ea4eb52d92
-- title:
--   Real-time extension of an admissible dividend path is measurable
-- statement:
--   The Stieltjes dividend measure is built from the real-time extension t ↦ D(t.toNNReal). For each scenario, this extension is measurable because the dividend strategy path is monotone, hence measurable on nonnegative time, and the clipping map from real to nonnegative real is measurable. This supplies a directly usable measurability prerequisite for stochastic stopping and controlled-reserve calculations.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_time_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_realTime_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Measurable (fun t : ℝ => D t.toNNReal ω) := by sorry
