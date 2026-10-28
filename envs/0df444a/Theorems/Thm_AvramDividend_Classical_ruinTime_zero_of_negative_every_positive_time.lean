-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_zero_of_negative_every_positive_time
-- name    : AvramDividend.Classical.ruinTime_zero_of_negative_every_positive_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:19:56.396861+00:00
-- url     : https://prove2.me/theorems/dfa7e3c4-5fec-4149-8d22-b2686312fe46
-- title:
--   Negative surplus at every positive time forces immediate ruin
-- statement:
--   For any controlled spectrally negative Lévy process, if its reserve is negative at every strictly positive time along one sample path, the ruin time equals zero on that sample path. The infimum of negative-reserve times is at most each positive time, hence is zero by order density of nonnegative real times in the extended nonnegative reals.
-- source:
--   Definition of controlled ruin time as the first strict negative-reserve time, together with order-density for extended nonnegative real times.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.ruinTime_zero_of_negative_every_positive_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hneg : ∀ t : ℝ≥0, 0 < t → riskProcess X x D t ω < 0) :
    ruinTime X x D ω = 0 := by sorry
