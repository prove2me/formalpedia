-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbMeas2_unitInterval_continuousMap_polish_instance
-- name    : AvramDividend.Classical.avram_gbMeas2_unitInterval_continuousMap_polish_instance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:52:06.023763+00:00
-- url     : https://prove2.me/theorems/12012e3f-c170-4b31-a12e-b8c9c25fa745
-- title:
--   Polish-space structure of real continuous paths on unit interval
-- statement:
--   The continuous-map space C(unitInterval,ℝ) is Polish in the pinned Mathlib topology. Its Polish structure is needed to apply Lusin–Souslin to the dense evaluation embedding, and thereby establish measurability of the native Brownian continuous-path lift from measurable coordinates.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbMeas2_unitInterval_continuousMap_polish_instance :
    PolishSpace C(unitInterval, ℝ) := by sorry
