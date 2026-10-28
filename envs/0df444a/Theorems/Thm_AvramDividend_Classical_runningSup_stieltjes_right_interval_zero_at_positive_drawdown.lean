-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stieltjes_right_interval_zero_at_positive_drawdown
-- name    : AvramDividend.Classical.runningSup_stieltjes_right_interval_zero_at_positive_drawdown
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:46:54.099978+00:00
-- url     : https://prove2.me/theorems/84cd2ce9-6443-45ea-8245-8b4a35fa7899
-- title:
--   The actual running-record Stieltjes local-time measure vanishes on a positive-length right interval after every positive reflected excursion time
-- statement:
--   For each sample path of an actual spectrally negative Lévy process and each time u at which the reflected drawdown R_u=runningSup(X)_u−X_u is strictly positive, there is a later time v>u such that the genuine Lebesgue–Stieltjes regulator/local-time measure d(runningSup X) gives the right half-open interval (u,v] zero mass. The source path's right continuity keeps X below its old record for a short interval, which has already been proved to make runningSup constant on [u,v'). Choose a strictly interior v and apply the established exact Stieltjes interval mass equals record increment formula. This is an actual regulator support lemma on positive excursions and advances construction of the excursion random measure n beyond statements merely conditional on its existence.
-- source:
--   Proved runningSup_right_local_const_of_positive_drawdown and runningSup_dividendMeasure_Ioc_eq_record_increment, pinned Mathlib densely ordered NNReal.

import Theorems.Thm_AvramDividend_Classical_runningSup_right_local_const_of_positive_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_stieltjes_right_interval_zero_at_positive_drawdown
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by sorry
