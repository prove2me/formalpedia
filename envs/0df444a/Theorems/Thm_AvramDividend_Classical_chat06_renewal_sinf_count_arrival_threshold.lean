-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_renewal_sinf_count_arrival_threshold
-- name    : AvramDividend.Classical.chat06_renewal_sinf_count_arrival_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:23:48.457154+00:00
-- url     : https://prove2.me/theorems/fddb92fd-8794-4c6e-bbd6-ab2f76c84cb2
-- title:
--   First future renewal-arrival index has exact completed-arrival threshold characterisation
-- statement:
--   Let the real-valued arrival-time sequence be nondecreasing and eventually strictly exceed a given time t. Define the renewal count as the least natural index of an arrival strictly after t. For each index k, the renewal count exceeds k if and only if the kth arrival has occurred by t. The strict/non-strict endpoints are exact, including times equal to an arrival. This is a foundational bridge from the infimum-based concrete compound-Poisson count to its finite-prefix threshold representation.
-- source:
--   bv_renewal_sinf_count_arrival_threshold_chat06_20261021.lean, 35 lines, 1101 bytes, SHA-256 c04ab69105311d007b9fd04079a379e2bc2a5caf6b4477b27b4b3d50d003e78a; private probe 96856c1b-37ff-4914-8aec-7c9a19f6884b passed sentinel without source errors.

import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic

open Set

theorem AvramDividend.Classical.chat06_renewal_sinf_count_arrival_threshold
    (arrival : ℕ → ℝ) (t : ℝ)
    (hmono : Monotone arrival)
    (hne : ∃ n : ℕ, t < arrival n)
    (k : ℕ) :
    k < sInf {n : ℕ | t < arrival n} ↔ arrival k ≤ t := by sorry
