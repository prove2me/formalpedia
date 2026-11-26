-- Prove2me | Theorems.Thm_Erdos287_ternary_positions_with_arbitrary_weight_separation
-- name    : Erdos287.ternary_positions_with_arbitrary_weight_separation
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:11:33.7903+00:00
-- url     : https://prove2.me/theorems/6ddc8149-1ee9-5c6a-bd9d-f4ba74b14cb1
-- title:
--   Ternary positions with arbitrary weight separation
-- statement:
--   Let $r>2$ be a natural number, and let $w_0,\ldots,w_{k-1}$ be positive integer weights with $w_{j+1}\ge(r+1)w_j$. There are $3^k$ distinct nonnegative integer positions at most $2\sum_j w_j$. For each positive distance $d$ between positions there is $j<k$ with $w_j(1-2/r)\le d\le 2w_j(1+1/r)$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. External sieve input: https://ford126.web.illinois.edu/sieve2023.pdf.

import Mathlib

theorem Erdos287.ternary_positions_with_arbitrary_weight_separation (w : ℕ → ℕ) (k r : ℕ) (hr : 2 < r)
    (hpos : ∀ j < k, 0 < w j)
    (hsep : ∀ j, j + 1 < k → (r + 1) * w j ≤ w (j + 1)) :
    ∃ S : Finset ℕ, S.card = 3 ^ k ∧
      (∀ x ∈ S, x ≤ 2 * ∑ j ∈ Finset.range k, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < k,
        r * w j ≤ r * (y - x) + 2 * w j ∧
        r * (y - x) ≤ r * (2 * w j) + 2 * w j := by sorry
