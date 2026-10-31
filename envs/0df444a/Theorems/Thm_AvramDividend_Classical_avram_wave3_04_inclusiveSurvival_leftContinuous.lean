-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_leftContinuous
-- name    : AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_leftContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:15:57.165863+00:00
-- url     : https://prove2.me/theorems/1e37ddbb-575f-4709-af51-ef11fff8e1a6
-- title:
--   Inclusive survival-clock indicator is left-continuous on nonnegative time
-- statement:
--   For any extended nonnegative clock τ, including τ=∞ and τ=0, the inclusive survival indicator 1_{s≤τ} is continuous from the left at every nonnegative time t. At the stopping clock the indicator remains one and the strict right-hand drop occurs only afterwards, so the predictable left-continuity convention is respected.
-- source:
--   Pinned Mathlib topology of ENNReal coercions and left-neighbourhood filters. Private remote compiler probe e2ad6a75-6718-43e8-a240-374ce3f3326a reached its intentional sentinel with no candidate errors, exact source SHA-256 52d48cf95deff0e0c7d3c6b4a2486ff31d9c757fc1db69b979b6ee3753aadaed.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_leftContinuous
    (τ : ℝ≥0∞) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0)
      (Set.Iic t) t := by sorry
