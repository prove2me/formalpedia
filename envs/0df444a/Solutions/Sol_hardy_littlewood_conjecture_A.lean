-- Prove2me | solution 1 for hardy_littlewood_conjecture_A
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:15:13.687768+00:00
-- url     : https://prove2.me/submissions/d52ac4d9-e18a-412d-9ed5-419dd6fb968c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution (k : ℕ) (hk : 0 < k) (hk2 : Even k) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite := by
  exact polignac_conjecture k hk hk2
