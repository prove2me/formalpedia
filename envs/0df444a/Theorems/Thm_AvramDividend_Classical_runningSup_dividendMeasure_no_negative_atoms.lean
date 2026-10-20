-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_negative_atoms
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_no_negative_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:21:55.946988+00:00
-- url     : https://prove2.me/theorems/e6ba84eb-ecf1-4f40-9747-5da5df7337ab
-- title:
--   No negative-time atoms in the actual extended running-supremum dividend measure
-- statement:
--   For every negative real time, the actual dividend Stieltjes measure of the running supremum has no singleton atom. The extension to real time by Real.toNNReal is constant on negative times. Its Stieltjes left limit equals its point value, so the Stieltjes singleton jump vanishes. This supplements no-nonnegative-time-atoms and supports endpoint-neutral partitioning.
-- source:
--   Proved actual Stieltjes measure identification and real-time right-limit equality; pinned StieltjesFunction.measure_singleton and leftLim_eq_of_tendsto.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_no_negative_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : t < 0) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by sorry
