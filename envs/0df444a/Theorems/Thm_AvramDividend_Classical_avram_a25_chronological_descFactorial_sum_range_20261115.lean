-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_chronological_descFactorial_sum_range_20261115
-- name    : AvramDividend.Classical.avram_a25_chronological_descFactorial_sum_range_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:52:31.623185+00:00
-- url     : https://prove2.me/theorems/798ad145-df16-4ab8-9cbd-512922e6a459
-- title:
--   Chronological jump count factorial identity as a sum of predictable prefix weights
-- statement:
--   If there are m ordered physical jumps, the (n+1)-st descending factorial of the final jump count is (n+1) times the sum over successive jump arrivals of the n-th descending factorial of the number of earlier jumps. This is the deterministic bridge between a predictable weighted source compensator (weight factorial of the pre-jump count) and the original final-count factorial-moment recurrence. Prove by induction on m using Finset.sum_range_succ and the chronological descending-factorial step.
-- source:
--   Pinned Mathlib Finset.sum_range_succ and chronological factorial increment theorem 9c27662d.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_chronological_descFactorial_step_20261115
open Nat AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a25_chronological_descFactorial_sum_range_20261115
    (m n : ℕ) :
    (n + 1) * (∑ k ∈ Finset.range m, Nat.descFactorial k n) =
      Nat.descFactorial m (n + 1) := by sorry
