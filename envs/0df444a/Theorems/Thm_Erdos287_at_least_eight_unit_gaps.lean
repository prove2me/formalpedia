-- Prove2me | Theorems.Thm_Erdos287_at_least_eight_unit_gaps
-- name    : Erdos287.at_least_eight_unit_gaps
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:32:16.982656+00:00
-- url     : https://prove2.me/theorems/38d3ff62-49b2-58f2-b41a-2213b4096151
-- title:
--   Any gap-at-most-two representation of one has at least eight unit gaps
-- statement:
--   Let $1<n_0<cdots<n_{k-1}$ be integers whose reciprocals sum to one, and suppose every successive gap is at most two. Then at least eight successive gaps are exactly one. This rules out the cases with two through seven unit gaps in the open residual problem for Erdős #287.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287; strengthened residual restriction using the parameterized free-prime argument of Reza Ramji (https://github.com/Zed-Rez/erdos-287-lean) and a verified interval cover by adjacent exclusions.

import Mathlib

theorem Erdos287.at_least_eight_unit_gaps (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) :
    8 ≤ ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by sorry
