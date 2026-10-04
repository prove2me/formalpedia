-- Prove2me | solution 4 for goldbach_odd_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T02:15:56.701679+00:00
-- url     : https://prove2.me/submissions/451f1bf1-86ec-44fe-b735-6e62add6593d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

theorem solution :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  intro n h7 hodd
  -- `Even n` is `n = r + r` for some `r`, and `r + r = 2 * r`, so a double
  -- witness is a `2 ∣ n` witness. Hence `¬ 2 ∣ n` rules out evenness outright,
  -- and `Nat.not_even_iff_odd` converts that into the `Odd n` both children want.
  have hne : ¬ Even n := by
    rintro ⟨r, hr⟩
    exact hodd ⟨r, by omega⟩
  have hodd' : Odd n := Nat.not_even_iff_odd.mp hne
  -- The split point is `10 ^ 27`, the analytic child's own floor, rather than
  -- the verified bound `B`. This is what keeps the argument free of any large
  -- numeral arithmetic: on the analytic side the branch hypothesis is already
  -- exactly `10 ^ 27 ≤ n`, so it is passed through unchanged, and the only
  -- numerical fact needed anywhere is the single dominance `10 ^ 27 ≤ B` that
  -- puts the sub-analytic side inside the verified window.
  rcases Nat.lt_or_ge n (10 ^ 27) with hsub | hfloor
  · -- Sub-analytic side: `n < 10 ^ 27`, and `10 ^ 27 ≤ B` places `n` strictly
    -- inside the verified window, so the verified child's upper bound follows.
    have hdom : 10 ^ 27 ≤ 8875694145621773516800000000000 := by norm_num
    have hns : n ≤ 10 ^ 27 := Nat.le_of_lt hsub
    have hmid : n ≤ 8875694145621773516800000000000 := Nat.le_trans hns hdom
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      WeakGoldbach.verified_three_primes_to_8875e30 n (Nat.le_of_lt h7) hmid hodd'
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
  · -- Analytic side: `hfloor` is already the child's floor in exactly the shape
    -- it declares, so it is forwarded without any conversion.
    obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.three_odd_primes_ge_10pow27 n hfloor hodd'
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
