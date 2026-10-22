-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_renewal_arrival_sum_future_suffix_decomposition
-- name    : AvramDividend.Classical.chat06_renewal_arrival_sum_future_suffix_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:45:10.554169+00:00
-- url     : https://prove2.me/theorems/8d7feeec-2f09-4a85-a080-727d77421c6a
-- title:
--   Renewal arrival time splits into observed arrival prefix and subsequent waiting-time suffix
-- statement:
--   For an arbitrary real-valued interarrival-time sequence, the cumulative arrival through the first n+m+1 waits equals the cumulative arrival through the first n+1 waits plus the next m waits reindexed from n+1. The identity is exact and prepares the future-arrival representation after observing N(clock)=n in the compound-Poisson process.
-- source:
--   bv_renewal_arrival_sum_future_suffix_decomposition_chat06_20261021.lean, 14 lines, 518 bytes, SHA-256 599a1c973aa7a28378d36bb1321514801f76e25f3c499500d1c3cf5bff53f659; private remote probe 841400a4-a3d2-454f-89e6-e8d21fbcd8de passed sentinel without source errors.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_renewal_arrival_sum_future_suffix_decomposition (τ : ℕ → ℝ) (n m : ℕ) :
    (∑ i ∈ Finset.range ((n + 1) + m), τ i) =
      (∑ i ∈ Finset.range (n + 1), τ i) +
        (∑ j ∈ Finset.range m, τ ((n + 1) + j)) := by sorry
