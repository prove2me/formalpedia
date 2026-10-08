-- Prove2me | Theorems.Thm_AvramDividend_Classical_rawRunningSup_interval_split
-- name    : AvramDividend.Classical.rawRunningSup_interval_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T18:47:13.85748+00:00
-- url     : https://prove2.me/theorems/fd791a13-6127-4e80-9301-48db0ae0947e
-- title:
--   Split a bounded real running supremum at a deterministic time
-- statement:
--   For a real-valued path bounded above on [0,u+t], the supremum over the full interval equals the maximum of its suprema over [0,u] and [u,u+t]. Real supremum boundedness is explicit. This is the deterministic-time decomposition needed for the shifted barrier dividend process at first passage.
-- source:
--   General conditionally complete real supremum splitting, used for Definitions.Def_AvramDividend_Classical_Reflection and AvramDividend.Classical.barrierStrategy_value_eq_exit_factor.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.rawRunningSup_interval_split
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove
      (Set.range (fun s : Set.Icc (0 : ℝ≥0) (u + t) => f s.1))) :
    (⨆ s : Set.Icc (0 : ℝ≥0) (u + t), f s.1) =
      max (⨆ s : Set.Icc (0 : ℝ≥0) u, f s.1)
          (⨆ s : Set.Icc u (u + t), f s.1) := by sorry
