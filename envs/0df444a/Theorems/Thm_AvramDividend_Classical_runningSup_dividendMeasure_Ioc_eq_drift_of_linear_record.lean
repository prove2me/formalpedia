-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:06:15.484928+00:00
-- url     : https://prove2.me/theorems/1af3e92b-3470-4842-8b13-44384176fd5e
-- title:
--   Actual linear running-record endpoints determine interval dividend mass
-- statement:
--   If the actual running supremum of the given Lévy process equals its deterministic drift line at two real-time endpoints, its Stieltjes dividend measure on the intervening half-open interval equals the nonnegative drift increment. Right limits are removed by the already proved right continuity of runningSup.
-- source:
--   Prove2Me Proved runningSup_dividendMeasure_Ioc_eq_linear_drift (01e557c8-79bc-43dc-97a8-4301290dcc9a) and runningSup_realTime_rightLim_eq (086548ed-c97c-4fb2-aa51-c0805cc917a5).

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_linear_drift
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ)
    (hs : runningSup X s.toNNReal ω = X.drift * s)
    (ht : runningSup X t.toNNReal ω = X.drift * t) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by sorry
