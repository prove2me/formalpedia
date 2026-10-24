-- Prove2me | Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
-- name    : AvramDividend.Classical.shiftedSup_increment_eq_sup_sub
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:25:54.250575+00:00
-- url     : https://prove2.me/theorems/78604350-c133-4845-ad1f-ed08f5123bc4
-- title:
--   Running supremum of shifted increments equals shifted record supremum less starting level
-- statement:
--   For an upper-bounded path on [u,u+t], taking the supremum of all increments f(u+r)−f(u) over r∈[0,t] is identical to taking the supremum of the absolute path values over the same interval and subtracting f(u). This specialises the general real-set supremum shift theorem to the actual post-first-passage process and is a direct prerequisite for the dividend-measure translation theorem.

import Mathlib.Data.NNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Set
open scoped NNReal

theorem AvramDividend.Classical.shiftedSup_increment_eq_sup_sub
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t)) :
    sSup ((fun r : ℝ≥0 => f (u + r) - f u) '' Set.Icc 0 t) =
      sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) - f u := by sorry
