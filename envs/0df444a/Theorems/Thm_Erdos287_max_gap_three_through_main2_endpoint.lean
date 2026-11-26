-- Prove2me | Theorems.Thm_Erdos287_max_gap_three_through_main2_endpoint
-- name    : Erdos287.max_gap_three_through_main2_endpoint
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:48:11.53249+00:00
-- url     : https://prove2.me/theorems/2a2672f2-e667-4124-937c-3d437aeb0fc8
-- title:
--   Continuous compact certificate through the Main2 endpoint
-- statement:
--   Every representation of $1$ by at least two strictly increasing integer denominators greater than $1$ has a gap at least three if its largest denominator is at most $858988211239796718174213$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.max_gap_three_through_main2_endpoint (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 858988211239796718174213) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
