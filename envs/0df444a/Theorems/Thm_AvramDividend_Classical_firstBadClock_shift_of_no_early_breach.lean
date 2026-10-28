-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
-- name    : AvramDividend.Classical.firstBadClock_shift_of_no_early_breach
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:02.85421+00:00
-- url     : https://prove2.me/theorems/23721444-7fc1-4613-b7d6-f5555ff3e76c
-- title:
--   First bad time shifts by a finite origin when no earlier bad event occurs
-- statement:
--   For any predicate bad on nonnegative time, if no bad event occurs strictly before a finite time u and the predicate at u+t agrees with a shifted future predicate at t, then the extended-nonnegative infimum of original bad times equals u plus the infimum of shifted bad times. This includes infinite clocks and first bad times at u. It is the precise order-theoretic time-translation lemma required to identify controlled barrier ruin after first upcrossing with the first bad time of the Lévy shifted-increment reflected reserve. No stochastic assumptions enter this result.
-- source:
--   General translation of an ENNReal-valued first-breach time, using pinned ENNReal.iInf_add and NNReal.add_tsub_cancel_of_le. Applies to Proved pathwise post-first-upcrossing controlled-surplus identity (6faad50b) and the standing barrier-value strong-Markov bridge (79978d61).

import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstBadClock_shift_of_no_early_breach
    (u : ℝ≥0) (bad shiftedBad : ℝ≥0 → Prop)
    (hpre : ∀ s : ℝ≥0, s < u → ¬ bad s)
    (hpost : ∀ t : ℝ≥0, bad (u + t) ↔ shiftedBad t) :
    (⨅ (s : ℝ≥0) (_ : bad s), (s : ℝ≥0∞)) =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0) (_ : shiftedBad t), (t : ℝ≥0∞)) := by sorry
