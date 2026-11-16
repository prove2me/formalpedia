-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_chronological_descFactorial_step_20261115
-- name    : AvramDividend.Classical.avram_a25_chronological_descFactorial_step_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:43:18.500841+00:00
-- url     : https://prove2.me/theorems/9c27662d-b82c-43df-9135-70003a40d514
-- title:
--   Chronological descending factorial increment for marked physical jump counts
-- statement:
--   A deterministic identity representing the increment of the (n+1)-st descending factorial when a new physical jump is appended after k earlier jumps. This is the combinatorial step for the original-source factorial-moment compensator recurrence, where the newly arriving jump contributes (n+1) times the n-th descending factorial of the pre-jump count. Valid for all k and n, including k<n.
-- source:
--   Pinned Mathlib Nat.succ_descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_eq_zero_iff_lt.

import Mathlib
open Nat
noncomputable section

theorem AvramDividend.Classical.avram_a25_chronological_descFactorial_step_20261115 (k n : ℕ) :
    Nat.descFactorial (k + 1) (n + 1) =
      Nat.descFactorial k (n + 1) + (n + 1) * Nat.descFactorial k n := by sorry
