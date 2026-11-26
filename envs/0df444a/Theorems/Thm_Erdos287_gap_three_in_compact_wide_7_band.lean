-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_7_band
-- name    : Erdos287.gap_three_in_compact_wide_7_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:58:56.939878+00:00
-- url     : https://prove2.me/theorems/89e7b3a7-66af-5298-b13f-e7e6f92ed23e
-- title:
--   Compact Lucas certificates for wide band 7
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[263588884858131783375371140402679714449945424711319890847933073159865856950104334566089736438554049862696956,214159363982694220762791838234441303966448576564395913178069362933275385011193945334184159829056850097682828246510469130]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide7.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_7_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 263588884858131783375371140402679714449945424711319890847933073159865856950104334566089736438554049862696956 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 214159363982694220762791838234441303966448576564395913178069362933275385011193945334184159829056850097682828246510469130) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
