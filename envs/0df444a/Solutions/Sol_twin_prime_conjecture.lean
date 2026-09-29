-- Prove2me | solution 1 for twin_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:21:38.877722+00:00
-- url     : https://prove2.me/submissions/926e587d-d1c3-4f6d-b3f1-720ec1b3cda2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := by
  simpa using polignac_conjecture 2 (by decide) (by decide)
