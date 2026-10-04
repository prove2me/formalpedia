-- Prove2me | solution 3 for goldbach_odd_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T01:44:10.375465+00:00
-- url     : https://prove2.me/submissions/75fac509-6fb2-454e-a6b8-2dcd4da25f54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_verified_three_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

theorem solution :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  intro n h7 hodd
  -- `Odd n` is the hypothesis both computational children want, but the target
  -- states oddness as `¬ 2 ∣ n`, and `Nat.not_even_iff_odd` is stated against
  -- `¬ Even n`. The bridge goes through the definition of `Even`: a double
  -- witness `n = r + r` is a `2 ∣ n` witness, since `r + r = 2 * r`.
  have hne : ¬ Even n := by
    rintro ⟨r, hr⟩
    exact hodd ⟨r, by omega⟩
  have hodd' : Odd n := Nat.not_even_iff_odd.mp hne
  -- The two children tile the range at the verified bound
  -- `B := 8875694145621773516800000000000`.
  rcases Nat.le_total n 8875694145621773516800000000000 with hmid | htail
  · -- Verified computational range. Its floor is `7 ≤ n`, which is `h7` read
    -- in the `≤` form the child signature asks for.
    obtain ⟨p, q, r, hp, hq, hr, hsum⟩ :=
      WeakGoldbach.verified_three_primes_to_8875e30 n (Nat.le_of_lt h7) hmid hodd'
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
  · -- Helfgott's analytic range. `htail` is already `B ≤ n`, and the verified
    -- bound dominates `10 ^ 27`, so the range floor is reached by transitivity
    -- instead of asking `omega` to reason about a 31-digit numeral. The
    -- transitivity step is written with an explicit intermediate `hdom` rather
    -- than with a named argument of `Nat.le_trans`, so that it does not depend
    -- on the elaborator's parameter naming for that lemma.
    have hdom : 10 ^ 27 ≤ 8875694145621773516800000000000 := by norm_num
    have hfloor : 10 ^ 27 ≤ n := by
      exact Nat.le_trans hdom htail
    obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.three_odd_primes_ge_10pow27 n hfloor hodd'
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
