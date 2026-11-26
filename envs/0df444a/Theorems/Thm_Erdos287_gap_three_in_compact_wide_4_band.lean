-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_4_band
-- name    : Erdos287.gap_three_in_compact_wide_4_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:56:02.196734+00:00
-- url     : https://prove2.me/theorems/e6ba9794-87d6-585e-99e9-01674158c882
-- title:
--   Compact Lucas certificates for wide band 4
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[459783374368222904827056593518393074552324179891101421807809742577336331,387705887984591711416546378186759000448837202053331156305529786801988604734377820170]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide4.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_4_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 459783374368222904827056593518393074552324179891101421807809742577336331 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 387705887984591711416546378186759000448837202053331156305529786801988604734377820170) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
