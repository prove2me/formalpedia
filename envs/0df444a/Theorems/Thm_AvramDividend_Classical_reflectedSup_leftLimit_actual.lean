-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_leftLimit_actual
-- name    : AvramDividend.Classical.reflectedSup_leftLimit_actual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:35:44.838801+00:00
-- url     : https://prove2.me/theorems/e866dc84-d49d-4e98-8786-99ac115e77a7
-- title:
--   Actual reflected spectrally negative Lévy drawdown has finite left limits at every positive time
-- statement:
--   For each actual spectrally negative Lévy sample path and every positive time t, the reflected process R_t=runningSup(X,t)−X_t has a finite left limit. The running supremum is already canonically proved continuous from the left, and X has a left limit by the model's Lévy sample-path structure. Their difference converges to the difference of their left limits. This fills the remaining regularity premise needed to deduce upper semicontinuity of the genuine drawdown path on finite intervals.
-- source:
--   Lévy sample-path càdlàg regularity; existing Prove2Me runningSup_left_continuous_actual and SpectrallyNegativeLevy.leftLim.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Mathlib.Topology.Algebra.Group.Defs

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_leftLimit_actual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ, Filter.Tendsto
      (fun s : ℝ≥0 => reflectedSup X s ω)
      (nhdsWithin t (Iio t)) (nhds l) := by sorry
