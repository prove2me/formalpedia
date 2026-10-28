-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_stopping_rightCont_filtration
-- name    : AvramDividend.Classical.barrierRuinTime_stopping_rightCont_filtration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:46:48.421338+00:00
-- url     : https://prove2.me/theorems/bd9bfa6b-08bb-4a9a-b9f6-e9160bc78bff
-- title:
--   Reflected barrier ruin is a stopping time in the right-continuous filtration
-- statement:
--   For a spectrally negative Lévy process and any barrier level, the ruin time of the running-supremum reflected reserve is a stopping time relative to the right-continuous modification of the given filtration. This follows from the identity between reflected ruin and ordinary ruin of the running-supremum strategy, its admissibility, and the existing stopping-time theorem for ruin. It makes stopped-survival events available for strong-Markov first-record renewal arguments.
-- source:
--   Apply the proved reflected-ruin identity and the general ruin-time stopping theorem to the running-supremum dividend strategy.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_stopping_rightCont_filtration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) :
    IsStoppingTime 𝓕.rightCont (barrierRuinTime X a) := by sorry
