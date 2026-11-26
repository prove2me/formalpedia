-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_2_band
-- name    : Erdos287.gap_three_in_compact_wide_2_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:54:36.557685+00:00
-- url     : https://prove2.me/theorems/c7e281b0-edd7-459c-8323-9d0508515206
-- title:
--   Compact Lucas certificates for wide band 2
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[638040061592254890692656715489809416283561656331,541652714334911275455338317345215128734636854357567010242570]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide2.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_2_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 638040061592254890692656715489809416283561656331 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 541652714334911275455338317345215128734636854357567010242570) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
