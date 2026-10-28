-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_no_downward_jumps_actual
-- name    : AvramDividend.Classical.reflectedSup_no_downward_jumps_actual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:35:13.350667+00:00
-- url     : https://prove2.me/theorems/68d7f1d6-14e4-43f9-9b64-87b9954b390c
-- title:
--   Actual spectrally negative Lévy reflected drawdown has no downward jumps
-- statement:
--   The actual reflected process R_t=runningSup(X,t)−X_t of a spectrally negative Lévy process has no downward jumps at positive times. Left continuity of the actual running supremum (already canonically proved), existence of the left limit X(t−), and the no-positive-jumps field X_t≤X(t−) establish R(t−)≤R_t. This removes the artificial global continuous-S hypothesis from the generic reflected no-downward-jump theorem and supplies the exact structural assumption for upper semicontinuity of the genuine reflected path.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) scale-function excursion theory; existing Prove2Me runningSup_left_continuous_actual and SpectrallyNegativeLevy leftLim/noPosJumps.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_actual
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_no_downward_jumps_actual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Filter.Tendsto (fun s : ℝ≥0 => reflectedSup X s ω)
        (nhdsWithin t (Iio t)) (nhds l) →
      l ≤ reflectedSup X t ω := by sorry
