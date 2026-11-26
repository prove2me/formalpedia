-- Prove2me | Theorems.Thm_Erdos287_gap_three_in_compact_wide_11_band
-- name    : Erdos287.gap_three_in_compact_wide_11_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:03:32.165041+00:00
-- url     : https://prove2.me/theorems/04c4941b-c842-490b-858c-7cd640c1b929
-- title:
--   Compact Lucas certificates for wide band 11
-- statement:
--   For an increasing representation of $1$ by at least two unit fractions with denominators greater than $1$, a gap is at least three if the maximum denominator lies in the exact closed interval $[103091558235810307556758383984131383502338270262018175758223050084115981815857437218079654870252928856883491762045970221421952527076000397762791792506306556,381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435]$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Wide11.lean.

import Mathlib

theorem Erdos287.gap_three_in_compact_wide_11_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 103091558235810307556758383984131383502338270262018175758223050084115981815857437218079654870252928856883491762045970221421952527076000397762791792506306556 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
