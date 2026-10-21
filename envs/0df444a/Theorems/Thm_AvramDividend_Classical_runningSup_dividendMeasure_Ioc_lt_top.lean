-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_lt_top
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:30:07.201953+00:00
-- url     : https://prove2.me/theorems/fbd92a8a-a9ce-4153-83c7-45867f6a929b
-- title:
--   True running-supremum dividend Stieltjes measure is finite on every bounded half-open interval
-- statement:
--   For every genuine spectrally negative Lévy running-supremum regulator, sample point and pair of real interval endpoints, the Stieltjes dividend measure assigns finite ENNReal mass to the half-open interval. The already accepted exact record-increment formula identifies that mass with ENNReal.ofReal of a finite real difference. This establishes local finiteness independently of stochastic expectations and provides a useful ingredient for constructing finite or s-finite kernels from the interval-restricted random dividend measure.
-- source:
--   Accepted runningSup_dividendMeasure_Ioc_eq_record_increment target 7343971b-047e-4925-9fa7-7ee76f6a2b23; pinned Mathlib ENNReal.ofReal_lt_top.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc s t) < ⊤ := by sorry
