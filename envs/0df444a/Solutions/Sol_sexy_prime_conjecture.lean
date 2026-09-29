-- Prove2me | solution 1 for sexy_prime_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T06:11:21.540439+00:00
-- url     : https://prove2.me/submissions/e188ff29-e26a-43af-8df7-95a4defd6aa6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polignac_conjecture

theorem solution :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 6)}.Infinite := by
  simpa using polignac_conjecture 6 (by decide) (by decide)
