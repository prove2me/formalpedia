-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_6_band
-- name    : Erdos287.gap_three_in_compact_wide_6_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:58:59.321028+00:00
-- url     : https://prove2.me/theorems/5e1c6b9a-b5b3-465f-a6f7-cc667e01f9d6
-- title:
--   Compact Lucas certificates for wide band 6
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[321044521188307171763396601049205737020336364359631570294888556356534994101563402720486002524156,263588884858131783375371140402679714449945424711319890847933073159865856950104334566089736438554049862696955]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide6.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_6_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 321044521188307171763396601049205737020336364359631570294888556356534994101563402720486002524156 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 263588884858131783375371140402679714449945424711319890847933073159865856950104334566089736438554049862696955) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
