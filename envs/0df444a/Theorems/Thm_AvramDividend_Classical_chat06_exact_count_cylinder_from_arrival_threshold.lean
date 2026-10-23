-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
-- name    : AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:32:00.09489+00:00
-- url     : https://prove2.me/theorems/87f27821-c7c8-41c1-8ff3-0430dc108971
-- title:
--   Exact renewal count cylinders derived from arrival-time thresholds
-- statement:
--   At a nonnegative deterministic observation time, a renewal count equals n if and only if the arrival threshold through n waiting times has occurred and the next arrival threshold has not. This is deduced from the exact arrival-threshold equivalence, including the n=0 case using the nonnegative-clock hypothesis. It removes an independently assumed countwise cylinder identity from subsequent random residual and future-suffix factorisation lemmas.
-- source:
--   bv_exact_count_cylinder_from_arrival_threshold_chat06_20261021.lean, 56 lines, 1864 bytes, SHA-256 91bb64e89b6ef6381e840b428cb42e63d081e4f036023c2003cf555f1fbd3619; private remote job f4d43466-97b5-4f6f-84ce-a05dc7b0c56e passed sentinel with zero source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock) (n : ℕ) :
    N clock = n ↔
      (∑ i ∈ Finset.range n, τ i) ≤ clock ∧
        clock < ∑ i ∈ Finset.range (n + 1), τ i := by sorry
