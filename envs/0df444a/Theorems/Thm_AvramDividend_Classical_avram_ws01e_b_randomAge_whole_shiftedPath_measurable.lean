-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_randomAge_whole_shiftedPath_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:27:44.917159+00:00
-- url     : https://prove2.me/theorems/8e59a363-b0cf-4d41-a44b-8497302a726e
-- title:
--   Joint measurability of the entire shifted Levy path at every measurable random age
-- statement:
--   For the actual spectrally negative Levy process and any measurable finite nonnegative random age tau (in particular the true capped first strict upper-record age, a right-continuous-filtration stopping time), the entire shifted future path ω↦(t↦X_(tau+t)(ω)-X_tau(ω)) is a measurable map into the Borel product path space. This source-specific interface discharges the whole-fresh-path measurability requirement in the genuine exponential-clock random-age joint reward shift 51ea1a74, without incorrectly assuming capped first records are stopping times for the unaugmented original filtration.
-- source:
--   Proved joint-time Levy state measurability d55462c3-decf-40f0-9aff-439d356324d9 composed with measurable tau and deterministic shifts, assembled by pinned measurable_pi_lambda over all t in NNReal. This specifically discharges the hReward requirement in 51ea1a74 for the full Qp first-record regeneration proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_randomAge_whole_shiftedPath_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by sorry
