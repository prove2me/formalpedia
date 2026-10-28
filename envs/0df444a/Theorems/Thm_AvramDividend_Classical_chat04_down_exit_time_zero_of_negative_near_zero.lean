-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero
-- name    : AvramDividend.Classical.chat04_down_exit_time_zero_of_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:53:04.869658+00:00
-- url     : https://prove2.me/theorems/ac9a5651-010e-4c40-b205-951565722f97
-- title:
--   Instantaneous strict downward exit from arbitrarily early negative Lévy values
-- statement:
--   If a sample path takes a strictly negative value before every positive time threshold, then the strict first downward-passage time below zero, represented by the double-indexed ENNReal infimum, is zero. This is the pathwise bridge from almost-sure regularity at the negative half-line to the root-connected two-sided stopped-scale boundary result.
-- source:
--   Direct prerequisite for Proved chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero (8029c619-18d2-4bb2-af3b-90196ce32411), which is a direct x=0 boundary specialisation of Open chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34-200b-4736-a369-5ae8473e3258), under parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7. Proof adapted from already Proved barrierRuinTime_zero_of_near_zero_drawdown (1fa70426-22a7-4003-98e1-939fdb2b0ae4), with exact strict exit double infimum.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_down_exit_time_zero_of_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hNear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    (⨅ (t : ℝ≥0) (_ : X.X t ω < 0), (t : ℝ≥0∞)) = 0 := by sorry
