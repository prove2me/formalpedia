-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_first_wide_band
-- name    : Erdos287.gap_three_in_compact_first_wide_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:49:56.678626+00:00
-- url     : https://prove2.me/theorems/7db90c1f-4a31-5583-b01d-5d44aeb4405b
-- title:
--   Compact Lucas certificates through the first wide band
-- statement:
--   Some adjacent gap is at least three in any strictly increasing positive unit-fraction representation of $1$ whose largest denominator lies between $858988211239796718174214$ and $740570313355511917542635417831997435$, inclusive.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide0.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_first_wide_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 858988211239796718174214 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 740570313355511917542635417831997435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
