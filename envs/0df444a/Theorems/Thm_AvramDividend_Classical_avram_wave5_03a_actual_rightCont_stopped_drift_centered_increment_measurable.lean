-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:46:57.787351+00:00
-- url     : https://prove2.me/theorems/23f45cdc-1c9e-45d4-9c5b-0979ef370772
-- title:
--   Actual right-continuously stopped original Levy drift-centred increment measurable
-- statement:
--   The same-source original spectrally negative Levy process has a measurable drift-centred future increment after any finite stopping time of its right-continuous filtration. Transport the source along the already Proved literal same-path right-continuous Levy lift, apply the original stopped future path measurability theorem, evaluate at deterministic h and subtract the constant h c. This is the measurability precondition for the genuine source Gaussian Fatou L2 limit identification; no independent Brownian process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_drift_centered_increment_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (h : ℝ≥0) :
    Measurable (fun ω : Ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) := by
  sorry
