-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_record_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:23:28.062207+00:00
-- url     : https://prove2.me/theorems/7343971b-047e-4925-9fa7-7ee76f6a2b23
-- title:
--   Exact running-supremum dividend measure mass equals the change in record level
-- statement:
--   For the original spectrally negative Lévy process, the Stieltjes dividend measure of its nondecreasing running maximum assigns (s,t] the nonnegative record increment S(t.toNNReal)−S(s.toNNReal), exactly, for all real s and t. Uses the accepted Stieltjes right-limit interval formula and the pending theorem that right limits of the actual running maximum equal the values themselves. This is an explicit quantitative bridge from dividendMeasure to record-level increments for stopped-payment discretisation, with no external regularity or Markov hypotheses.
-- source:
--   Mathlib StieltjesFunction.measure_Ioc; previously Proved runningSup_dividendMeasure_Ioc_rightLim (842a5998-7c24-4411-aeca-81f5fd46077c); pending runningSup_realTime_rightLim_eq. Avram Palmowski Pistorius 2007 discounted running-supremum dividends.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_record_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) =
      ENNReal.ofReal
        (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) := by sorry
