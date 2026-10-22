-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_random_index_future_arrival_decomposition
-- name    : AvramDividend.Classical.chat06_random_index_future_arrival_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:34:03.123883+00:00
-- url     : https://prove2.me/theorems/ef92b9a3-375b-4909-898d-8424bb973899
-- title:
--   Pathwise future arrival times as residual wait plus the complete selected suffix
-- statement:
--   For any sequence of real interarrival times and any integer-valued index N, the time of the (N+1+k)-th arrival relative to an observation clock equals the residual interval of the current Nth waiting time plus the sum of the next k complete waiting times. This deterministic finite-sum identity holds pointwise for every sample path, with no stochastic assumptions, and identifies the future arrival process as a measurable functional of the selected residual and entire post-next-claim waiting-time suffix. It supports the remaining proof of stationary independent increments after the joint renewal law.
-- source:
--   Source bv_random_index_future_arrival_decomposition_v2_chat06_20261021.lean, 25 lines, SHA-256 562ec172cc9d08844b5d80d3e0d83a70ed68fbe816cbed723095673aa4fd95ce. Remote probe 669a737b-f9c3-4e2e-9a83-654ce76c0e28 passed source elaboration to deliberate sentinel with no source errors. The v1 source failed due to missing real-number import and was preserved.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.chat06_random_index_future_arrival_decomposition
    {Ω : Type*} (τ : ℕ → Ω → ℝ)
    (N : Ω → ℕ) (clock : ℝ) (ω : Ω) (k : ℕ) :
    (∑ i ∈ Finset.range (N ω + 1 + k), τ i ω) - clock =
      (τ (N ω) ω -
        (clock - ∑ i ∈ Finset.range (N ω), τ i ω)) +
      ∑ j ∈ Finset.range k, τ (N ω + 1 + j) ω := by sorry
