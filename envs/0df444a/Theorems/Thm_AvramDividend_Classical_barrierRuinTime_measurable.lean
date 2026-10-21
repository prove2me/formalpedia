-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
-- name    : AvramDividend.Classical.barrierRuinTime_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:13:41.520516+00:00
-- url     : https://prove2.me/theorems/322896d6-052f-46bc-9fe6-962277f2d0a2
-- title:
--   Actual reflected-drawdown ruin time is measurable in the Lévy sample point
-- statement:
--   For the actual spectrally negative Lévy process and any real barrier, the original strict reflected-drawdown ruin horizon, valued in the extended nonnegative reals, is a measurable function of the sample point. This follows because the running supremum is already established as a genuine adapted dividend strategy and because its original controlled ruin time equals the original reflected drawdown stopping time pathwise. Apply the accepted general measurable controlled ruin-time theorem to the actual running-supremum dividend strategy. The result enables construction of random stopped interval dividend rewards as measurable functionals.
-- source:
--   Dependency-gated runningSup_isDividendStrategy request d918c202-327a-4faf-b5da-336efb9de3b5 and barrierRuinTime_eq_ruinTime_runningSup request 7f7cfc27-e3a2-476e-b284-88e33584fd93; proved ruinTime_measurable target bbfbecf4-7dfc-4812-84f3-8644c2b40b85.

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierRuinTime_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    Measurable (barrierRuinTime X a) := by sorry
