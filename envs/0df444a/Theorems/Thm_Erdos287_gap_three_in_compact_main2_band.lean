-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_main2_band
-- name    : Erdos287.gap_three_in_compact_main2_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:43:42.383328+00:00
-- url     : https://prove2.me/theorems/da85e625-254e-4468-a18d-a9060795a859
-- title:
--   Compact Lucas certificates through the Main2 endpoint
-- statement:
--   In a strictly increasing unit-fraction representation of $1$ by at least two integer denominators greater than $1$, some gap is at least three if the largest denominator lies in the exact interval $[382613444,858988211239796718174213]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Main2.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_main2_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 382613444 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 858988211239796718174213) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
