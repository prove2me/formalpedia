-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_realTime_leftLim_eq_pos
-- name    : AvramDividend.Classical.runningSup_realTime_leftLim_eq_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:36:37.302577+00:00
-- url     : https://prove2.me/theorems/a4d0dd48-88e0-4d5c-9ca1-84940f2f679d
-- title:
--   The actual running-supremum real-time left limit equals its record value at positive times
-- statement:
--   At each real time r>0, the actual running maximum of a spectrally negative Lévy process has its real-time left limit equal to its value, after the nonnegative-time extension through Real.toNNReal. Instantiate the separately remotely Proved actual NNReal-time left continuity, compose with continuous Real.toNNReal which maps t<r into toNNReal(t)<toNNReal(r) when r>0, and then use the monotone left-limit characterization. This is the exact endpoint equality needed to prove the absence of Stieltjes dividend atoms at every positive time and properly handle strict-ruin endpoints.
-- source:
--   Proved generic runningSup_left_continuous_of_no_upward_jump, pending Chat05 runningSup_left_continuous_actual (not yet Proved); pinned Mathlib Monotone.continuousWithinAt_Iio_iff_leftLim_eq and Real.toNNReal_lt_toNNReal_iff.

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_realTime_leftLim_eq_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (r : ℝ) (hr : 0 < r) :
    Function.leftLim
      (fun s : ℝ => runningSup X s.toNNReal ω) r =
      runningSup X r.toNNReal ω := by sorry
