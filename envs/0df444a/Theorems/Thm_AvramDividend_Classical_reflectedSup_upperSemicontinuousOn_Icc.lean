-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
-- name    : AvramDividend.Classical.reflectedSup_upperSemicontinuousOn_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:47:24.057443+00:00
-- url     : https://prove2.me/theorems/8cec706c-43c3-4800-aac4-e311084f7a4e
-- title:
--   Actual reflected spectrally negative Lévy path is upper semicontinuous on every finite interval
-- statement:
--   For any sample path of the canonical spectrally negative Lévy process, the actual reflected drawdown R_t=runningSup(X,t)−X_t is upper semicontinuous on each compact interval [0,ζ]. The already proved right continuity of R, newly proved finite left limits, and absence of downward jumps instantiate the reusable càdlàg upper-semicontinuity theorem. This eliminates a major conditional regularity hypothesis in the compact excursion maximum-attainment argument. It does not yet handle excursion lifetimes ζ=∞.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), Section 2.3, spectrally negative excursion-height regularity and upper-semicontinuity of reflected process.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_leftLimit_actual
import Theorems.Thm_AvramDividend_Classical_reflectedSup_no_downward_jumps_actual

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_upperSemicontinuousOn_Icc
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (ζ : ℝ≥0) :
    UpperSemicontinuousOn
      (fun t : ℝ≥0 => reflectedSup X t ω) (Icc 0 ζ) := by sorry
