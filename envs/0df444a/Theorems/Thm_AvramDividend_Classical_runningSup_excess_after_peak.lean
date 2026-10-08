-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_excess_after_peak
-- name    : AvramDividend.Classical.runningSup_excess_after_peak
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:17:44.249561+00:00
-- url     : https://prove2.me/theorems/8b33142d-ca6f-4b21-b428-2138ca88a383
-- title:
--   Excess running supremum after a peak equals the reflected shifted-path maximum
-- statement:
--   For any bounded-above real-valued path f on nonnegative times, if its running supremum at time u is attained at f(u), then the further increase in running supremum by time u+t equals the positive part of the shifted interval supremum minus f(u). This is the deterministic incremental-dividend identity at an attained barrier crossing before applying strong Markov.
-- source:
--   Pathwise consequences of the separately published interval splitting runningSup_split_at and time translation runningSup_interval_shift lemmas, plus lattice maximum algebra. No stopping time or law equivalence assumed.

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_excess_after_peak
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove (f '' Set.Icc 0 (u + t)))
    (hpeak : sSup (f '' Set.Icc 0 u) = f u) :
    sSup (f '' Set.Icc 0 (u + t)) - f u =
      max 0 (sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) - f u) := by sorry
