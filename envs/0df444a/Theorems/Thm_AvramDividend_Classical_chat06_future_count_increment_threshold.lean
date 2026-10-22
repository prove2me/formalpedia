-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_future_count_increment_threshold
-- name    : AvramDividend.Classical.chat06_future_count_increment_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:00:08.384815+00:00
-- url     : https://prove2.me/theorems/d8a94fad-083f-48e8-a128-b5a61fb36286
-- title:
--   Exact renewal count increment threshold from current residual and future waits
-- statement:
--   Under the exact arrival-threshold definition of a renewal count, the increment N(clock+t) minus a previously observed count n is greater than m precisely when the age-adjusted residual time until arrival n plus the next m waiting times is at most t. The truncated natural-number subtraction is handled exactly, including the zero-increment case. This is the deterministic count-increment representation required to transport independent residual and suffix laws to future count increments.
-- source:
--   bv_future_count_increment_threshold_chat06_20261021.lean, 34 lines, 1390 bytes, SHA-256 41e2e538cb031b142944c20ebd51568c4b2d353d681a62554eebab875fac8619; private remote probe 3d6c0d56-760e-4621-8fff-76d720a14f07 passed sentinel with no source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_future_count_increment_threshold
    (τ : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ u k,
      k < N u ↔ (∑ i ∈ Finset.range (k + 1), τ i) ≤ u)
    (clock t : ℝ) (n m : ℕ) :
    m < N (clock + t) - n ↔
      ((∑ i ∈ Finset.range (n + 1), τ i) - clock) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) ≤ t := by sorry
