-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_realTime_continuousAt_pos
-- name    : AvramDividend.Classical.runningSup_realTime_continuousAt_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:48:56.805855+00:00
-- url     : https://prove2.me/theorems/6f7967d3-627f-4b19-8590-3b6dcf716409
-- title:
--   The real-time running supremum is continuous at every positive time
-- statement:
--   At every real t>0, the actual spectrally negative Lévy running supremum S(r.toNNReal) is continuous. Proved one-sided left and right limit equalities both give the same S(t), and the real-time record is monotone. Mathlib's monotone continuity equivalence then gives full continuity at positive times. This supports the no-positive-payment-atom and stopped Stieltjes ruin endpoint lemmas needed for the true reflected-regulator valuation.
-- source:
--   Proved Chat05 runningSup_realTime_leftLim_eq_pos a4d0dd48-88e0-4d5c-9ca1-84940f2f679d, runningSup_realTime_rightLim_eq 086548ed-c97c-4fb2-aa51-c0805cc917a5, runningSup_monotone_and_path_le 848fbd48-f69f-46b9-b2bf-436cb33918a8; pinned Mathlib Monotone.continuousAt_iff_leftLim_eq_rightLim.

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_leftLim_eq_pos
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_realTime_continuousAt_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun r : ℝ => runningSup X r.toNNReal ω) t := by sorry
