-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_renewal_arrival_threshold_count_monotone
-- name    : AvramDividend.Classical.chat06_renewal_arrival_threshold_count_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:42:01.758983+00:00
-- url     : https://prove2.me/theorems/1cbeed13-b6f8-427f-845c-e9f470b07656
-- title:
--   Exact arrival-threshold characterisation implies renewal counting path is nondecreasing
-- statement:
--   If a counting process has the exact property k<N(t) if and only if the kth arrival occurs by t, then the count is nondecreasing in observation time. An assumed decrease would make the index N(t) both strictly smaller than the earlier count and strictly smaller than itself after applying the threshold at t.
-- source:
--   bv_renewal_arrival_threshold_count_monotone_v2_chat06_20261021.lean, 697 bytes, SHA-256 f655674f03f3007f5680b9c29ae8a7080753582e7c9f8bf6017007210bcf744a; original source independently passed private remote elaboration, corresponding v2 preconfigured diagnostic-option private probe 22fb9901-571d-4218-81ac-ab4d0e579e88 pending.

import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_renewal_arrival_threshold_count_monotone
    (arrival : ℕ → ℝ) (N : ℝ → ℕ)
    (hThreshold : ∀ t k, k < N t ↔ arrival k ≤ t) :
    Monotone N := by sorry
