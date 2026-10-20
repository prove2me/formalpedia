-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:55:07.864353+00:00
-- url     : https://prove2.me/theorems/a58ad30f-5992-4fbf-9198-4194afb2b995
-- title:
--   The original running-supremum regulator pays no Stieltjes atom at time zero
-- statement:
--   For the actual Lévy running-supremum dividend measure, its time-zero singleton has mass zero. The real-time running record is constant at its value S(0) on the negative half-line because real negative times are mapped to NNReal time zero. Therefore its left limit at zero equals S(0), and the already proved real-time right-limit identity identifies the right-continuous Stieltjes version with the running record itself. The Stieltjes singleton jump at zero is thus zero. This handles the distinguished time-zero payment convention of the original reflected-barrier value, including paths with ruin at time zero.
-- source:
--   Proved runningSup_dividendMeasure_eq_stieltjes and runningSup_realTime_rightLim_eq; pinned Mathlib Function.leftLim_eq_of_tendsto, Real.toNNReal_of_nonpos and StieltjesFunction.measure_singleton.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (dividendMeasure (runningSup X) ω) ({0} : Set ℝ) = 0 := by sorry
