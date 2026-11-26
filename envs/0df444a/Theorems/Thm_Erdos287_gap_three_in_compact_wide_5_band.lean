-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_5_band
-- name    : Erdos287.gap_three_in_compact_wide_5_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:59:00.1689+00:00
-- url     : https://prove2.me/theorems/f5c9b532-5fe3-4fef-878d-edcd53041c86
-- title:
--   Compact Lucas certificates for wide band 5
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[387705887984591711416546378186759000448837202053331156305529786801988604734377820171,321044521188307171763396601049205737020336364359631570294888556356534994101563402720486002524155]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide5.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_5_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 387705887984591711416546378186759000448837202053331156305529786801988604734377820171 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 321044521188307171763396601049205737020336364359631570294888556356534994101563402720486002524155) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
