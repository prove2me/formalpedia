-- Prove2me | Theorems.Thm_Erdos287_gap_one_count_of_large_max
-- name    : Erdos287.gap_one_count_of_large_max
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T02:29:30.033808+00:00
-- url     : https://prove2.me/theorems/0d157817-d0c8-4fbf-98f4-a7503a103707
-- title:
--   Arbitrarily many unit gaps for large denominators in Erdős 287
-- statement:
--   Suppose a strictly increasing list of integers greater than one represents one as a sum of reciprocal terms, and every successive gap is at most two. Let $M$ be its largest denominator. Given any $r\ge 0$, put $B=4(r+2)$ and $L=\operatorname{lcm}(1,\ldots,B)$. Then
--   $$
--   M\ge B(BL+1)\quad\Longrightarrow\quad
--   \#\{i:n_{i+1}-n_i=1\}\ge r.
--   $$
--   In particular, for each fixed bound on the number of unit gaps the largest denominator is bounded.
-- source:
--   Generalized from Reza Ramji, Bertrand134.g1_ge_134, https://github.com/Zed-Rez/erdos-287-lean/blob/main/P287/Bertrand134.lean. Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.gap_one_count_of_large_max (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (r : ℕ)
    (hM : let B := 4 * (r + 2); B * (B * Nat.lcmUpto B + 1) ≤ f (k - 1)) :
    r ≤ ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card := by sorry
