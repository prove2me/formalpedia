-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
-- name    : AvramDividend.Classical.ruinTime_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:47:32.839833+00:00
-- url     : https://prove2.me/theorems/bbfbecf4-7dfc-4812-84f3-8644c2b40b85
-- title:
--   Measurability of the controlled ruin time
-- statement:
--   For any dividend strategy, the ENNReal-valued first time at which the controlled reserve is negative is measurable. Its strict sublevel events are countable unions of fixed-time negative-reserve events over nonnegative rational times.
-- source:
--   Measure-theoretic helper for deterministic-horizon dividend payoff measurability in Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_lt_iff_exists_rat_negative

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (ruinTime X x D) := by sorry
