-- Prove2me | solution 1 for cousin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:11:41.634952+00:00
-- url     : https://prove2.me/submissions/96d09403-43c3-4396-a8da-efeaceb8c441
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 4)}.Infinite := by
  simpa using polignac_conjecture 4 (by decide) (by decide)
