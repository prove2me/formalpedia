-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_1_band
-- name    : Erdos287.gap_three_in_compact_wide_1_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:54:38.673828+00:00
-- url     : https://prove2.me/theorems/9ca8f067-3475-58b0-b354-6b244bdb8c9a
-- title:
--   Compact Lucas certificates for wide band 1
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[740570313355511917542635417831997436,638040061592254890692656715489809416283561656330]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide1.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_1_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 740570313355511917542635417831997436 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 638040061592254890692656715489809416283561656330) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
