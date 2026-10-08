-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_measurable
-- name    : AvramDividend.Classical.dividendMeasure_Ioc_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:49:46.289549+00:00
-- url     : https://prove2.me/theorems/b954e92f-2318-4b8e-9e56-322147b6d602
-- title:
--   Measurability of random dividend Stieltjes mass on a fixed interval
-- statement:
--   For a dividend strategy, the Lebesgue–Stieltjes dividend measure assigned to any fixed half-open interval (a,b] is a measurable ENNReal-valued function of the sample point. The interval mass is the positive part of the difference of the real-time extended dividend path's Stieltjes right limits at b and a.
-- source:
--   Measure-theoretic helper for Proposition 4(i), used to construct the random dividend measure as a measurable measure-valued map and prove deterministic-horizon dividend payoff measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ioc_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) :
    Measurable (fun ω => dividendMeasure D ω (Ioc a b)) := by sorry
