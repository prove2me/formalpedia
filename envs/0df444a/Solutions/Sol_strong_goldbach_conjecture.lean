-- Prove2me | solution 1 for strong_goldbach_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T00:13:03.111997+00:00
-- url     : https://prove2.me/submissions/c27cafc6-338d-484f-a801-a0aadff1d9e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_goldbach

theorem solution :
    ∀ n : ℕ, 4 ≤ n → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n hn hdiv
  apply goldbach n (by omega)
  exact (even_iff_two_dvd).2 hdiv
