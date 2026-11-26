-- Prove2me | Theorems.Thm_Erdos287_max_gap_three_through_main3_endpoint
-- name    : Erdos287.max_gap_three_through_main3_endpoint
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:06:10.587953+00:00
-- url     : https://prove2.me/theorems/f82a82c8-a78f-4a1c-bde3-d7321405e525
-- title:
--   Continuous Lean certificate through the Main3 endpoint
-- statement:
--   Any strictly increasing unit-fraction representation of $1$ by at least two denominators greater than $1$ has an adjacent gap of at least three if its largest denominator is at most $381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435$.
-- source:
--   Reza Ramji, erdos-287-lean, https://github.com/Zed-Rez/erdos-287-lean/blob/2b2ecb1022cc3bfe249d9733003d3488f2d3027f/P287/Main3.lean.

import Mathlib

theorem Erdos287.max_gap_three_through_main3_endpoint (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hbound : f (k - 1) ≤ 381185219244960776204622798194589878857417272332616682539469868641615417785666328820964948335432532885427126626573411739149117629379557737669727589422795325435) : ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
