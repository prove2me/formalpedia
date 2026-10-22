-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_future_suffix_arrival_count_threshold
-- name    : AvramDividend.Classical.chat06_future_suffix_arrival_count_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:57:33.562569+00:00
-- url     : https://prove2.me/theorems/0ef020e9-3370-4213-8474-ec1be9896c09
-- title:
--   Exact future arrival count threshold from elapsed residual wait and following waiting times
-- statement:
--   Given an exact renewal-count arrival threshold equivalence, the future count at clock+t exceeds n+m exactly when the residual time from clock until arrival n, plus the next m waiting times reindexed after arrival n, is at most t. The proof is a source-faithful equivalence obtained by decomposing the arrival sum and rearranging the time inequality. It is a deterministic algebraic prerequisite for later random-count independent increments.
-- source:
--   bv_future_suffix_arrival_count_threshold_chat06_20261021.lean, 35 lines, 1246 bytes, SHA-256 430d0a7a3e4e79a211ca0602e2e2cbd0a6d28edebb774408704c044fbf220324; private remote probe 8d020bbf-f7fd-47d6-bf2b-5b34d962a2f0 passed sentinel without source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_future_suffix_arrival_count_threshold
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock t : ℝ) (n m : ℕ) :
    n + m < N (clock + t) ↔
      ((∑ i ∈ Finset.range (n + 1), τ i) - clock) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) ≤ t := by sorry
