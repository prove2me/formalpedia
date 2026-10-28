-- Prove2me | Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_sup_ge
-- name    : AvramDividend.Classical.usc_compact_prefix_hit_iff_sup_ge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:08:57.440993+00:00
-- url     : https://prove2.me/theorems/6b277e06-3f53-47fe-a093-23859bbe7432
-- title:
--   Closed level hit by a compact upper semicontinuous path is equivalent to its prefix supremum reaching that level
-- statement:
--   For any real-valued upper-semicontinuous path R over the compact nonnegative-time interval [0,t], reaching level x at some time up to t is equivalent to the exact supremum of R on that interval being at least x. Forward direction uses le_csSup and compactness. Reverse direction uses the accepted uniform strict-prefix gap theorem: if the path stayed strictly below x everywhere, its compact supremum would itself be strictly below x. This is the essential event equivalence for proving continuous-time reflected first-height passage is observable from a dense countable schedule.
-- source:
--   Pinned Mathlib compact USC boundedness and le_csSup, accepted AvramDividend.Classical.usc_compact_prefix_sup_strictly_below_level.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_sup_strictly_below_level

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.usc_compact_prefix_hit_iff_sup_ge
    (R : ℝ≥0 → ℝ) (t : ℝ≥0) (x : ℝ)
    (husc : UpperSemicontinuousOn R (Icc 0 t)) :
    (∃ s : ℝ≥0, s ≤ t ∧ x ≤ R s) ↔
      x ≤ sSup (R '' Icc (0 : ℝ≥0) t) := by sorry
