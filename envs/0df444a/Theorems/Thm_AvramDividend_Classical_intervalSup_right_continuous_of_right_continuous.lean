-- Prove2me | Theorems.Thm_AvramDividend_Classical_intervalSup_right_continuous_of_right_continuous
-- name    : AvramDividend.Classical.intervalSup_right_continuous_of_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:06:34.796178+00:00
-- url     : https://prove2.me/theorems/b28b6185-6d44-44d2-b25c-881eb1733a15
-- title:
--   Running supremum over bounded time intervals is right-continuous
-- statement:
--   If a real-valued path on nonnegative time is right-continuous and bounded above on every initial compact interval, then the path of its running supremum, expressed as sSup over each interval [0,t], is itself right-continuous. This bridges the generic running supremum continuity theorem to the exact supremum form used for shifted dividend rewards.

import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Mathlib.Order.CompleteLattice.Basic

open Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.intervalSup_right_continuous_of_right_continuous
    (f : ℝ≥0 → ℝ)
    (hB : ∀ t : ℝ≥0, BddAbove (f '' Set.Icc 0 t))
    (hf : ∀ t : ℝ≥0, Tendsto f (𝓝[≥] t) (𝓝 (f t))) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => sSup (f '' Set.Icc 0 s)) (Set.Ici t) t := by sorry
