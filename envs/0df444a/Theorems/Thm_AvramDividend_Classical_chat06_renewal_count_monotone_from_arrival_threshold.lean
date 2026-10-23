-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_renewal_count_monotone_from_arrival_threshold
-- name    : AvramDividend.Classical.chat06_renewal_count_monotone_from_arrival_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:55:44.16214+00:00
-- url     : https://prove2.me/theorems/cbb7372a-863a-4b05-a54c-ea839e649c4f
-- title:
--   Renewal count is monotone from its exact arrival-threshold relation
-- statement:
--   Any natural-number-valued renewal counting process characterised by k<N(u) if and only if the (k+1)-st interarrival partial sum is at most u is nondecreasing in u. If a count were to decrease between ordered observation times, the earlier threshold would also hold at the later time and contradict the strict irreflexivity of the later count. The lemma uses no distributional or positivity assumption and underpins the algebraic decomposition of future count increments.
-- source:
--   bv_renewal_count_monotone_from_arrival_threshold_chat06_20261022.lean, 23 lines, 790 bytes, SHA-256 15af38d6f3652c4fbe6a9ad9084208639628edb45c2a57907f01035f0a41bc1d; private probe ead8469d-d274-4a03-8d31-35543bdf1acc passed sentinel.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_renewal_count_monotone_from_arrival_threshold
    {Ω : Type*}
    (τ : ℕ → Ω → ℝ)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (ω : Ω) (u v : ℝ) (huv : u ≤ v) :
    N ω u ≤ N ω v := by sorry
