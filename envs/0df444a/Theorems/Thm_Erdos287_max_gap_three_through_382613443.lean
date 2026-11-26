-- Prove2me | Theorems.Thm_Erdos287_max_gap_three_through_382613443
-- name    : Erdos287.max_gap_three_through_382613443
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:27:56.920852+00:00
-- url     : https://prove2.me/theorems/f4539914-4acc-509e-9355-73d9d392e501
-- title:
--   Initial certified gap-three range through 382613443
-- statement:
--   Every representation of $1$ by at least two strictly increasing integer denominators greater than $1$ has a gap of at least three if its largest denominator is at most $382613443$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Main.lean#L15-L28.

import Mathlib

theorem Erdos287.max_gap_three_through_382613443 (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 382613443) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
