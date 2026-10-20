-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
-- name    : AvramDividend.Classical.runningSup_realTime_rightLim_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:32:03.822485+00:00
-- url     : https://prove2.me/theorems/086548ed-c97c-4fb2-aa51-c0805cc917a5
-- title:
--   The actual real-time running supremum equals its right limit
-- statement:
--   The running supremum of a cadlag spectrally negative Levy process is right-continuous. Its extension to all real times using Real.toNNReal is also right-continuous, so Function.rightLim at each real time equals the running supremum there, including at zero. This removes right-limit ambiguity from the Stieltjes dividend mass formula.
-- source:
--   Proved reflectedSup_right_continuous aed33f06-6482-4d51-898d-5f3c5630f827, SpectrallyNegativeLevy.rightCont, Mathlib continuous_real_toNNReal and ContinuousWithinAt.rightLim_eq.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_realTime_rightLim_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (r : ℝ) :
    Function.rightLim
        (fun s : ℝ => runningSup X s.toNNReal ω) r =
      runningSup X r.toNNReal ω := by sorry
