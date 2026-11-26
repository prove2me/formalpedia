-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_3_band
-- name    : Erdos287.gap_three_in_compact_wide_3_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:54:38.70336+00:00
-- url     : https://prove2.me/theorems/339a6b84-22bb-4e0b-a5cb-cc0aedcbc80c
-- title:
--   Compact Lucas certificates for wide band 3
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[541652714334911275455338317345215128734636854357567010242571,459783374368222904827056593518393074552324179891101421807809742577336330]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide3.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_3_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 541652714334911275455338317345215128734636854357567010242571 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 459783374368222904827056593518393074552324179891101421807809742577336330) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
