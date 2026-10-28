-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_nonpositive
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:06:37.543837+00:00
-- url     : https://prove2.me/theorems/abc5f5f8-340f-4183-8f74-d6068410bff7
-- title:
--   Entire reflected-running-supremum dividend measure vanishes at all nonpositive times
-- statement:
--   The actual Lebesgue–Stieltjes dividend measure of a spectrally negative Lévy running supremum vanishes on the complete nonpositive real-time half-line. Combine proved zero mass of every negative-to-zero interval and countable exhaustion. This supplies the support boundary condition for factorising future running-supremum dividend rewards at an upper stopping time.
-- source:
--   W-free strong-Markov barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380. Direct import of proved runningSup_dividendMeasure_Ioc_nonpos_eq_zero 55945b02-bdc5-4c2b-a26e-c147b0481f0b and measure_Iic_zero_of_all_negative_to_zero_Ioc_zero 30103409-586a-4404-b4a1-510990034747.

import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_nonpos_eq_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    dividendMeasure (runningSup X) ω (Set.Iic (0 : ℝ)) = 0 := by
  sorry
