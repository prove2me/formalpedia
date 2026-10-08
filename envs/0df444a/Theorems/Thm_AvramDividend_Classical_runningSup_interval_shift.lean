-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_interval_shift
-- name    : AvramDividend.Classical.runningSup_interval_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:12:28.549985+00:00
-- url     : https://prove2.me/theorems/a759cd2b-a458-4ffc-a439-3bed29e8bbfa
-- title:
--   Shift the real supremum over a post-passage interval to increments after its start
-- statement:
--   For any real-valued function of nonnegative time, the supremum of its values over [u,u+t] equals the supremum of the time-shifted function r↦f(u+r) over [0,t]. This exact image-of-interval equality includes both endpoints and is a deterministic prerequisite for shifting reflected dividends after first upcrossing.
-- source:
--   Elementary time-interval translation using tsub_le_iff_right and add_tsub_cancel_of_le from pinned Mathlib; independent of any Markov assumption.

import Mathlib

open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_interval_shift
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0) :
    sSup (f '' Set.Icc u (u + t)) =
      sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) := by sorry
