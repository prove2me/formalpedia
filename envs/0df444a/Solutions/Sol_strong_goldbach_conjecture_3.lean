-- Prove2me | solution 3 for strong_goldbach_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T00:52:19.583854+00:00
-- url     : https://prove2.me/submissions/9ac4f14e-a946-4896-bf82-a0a59ad2b730
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_goldbach

theorem solution :
    ∀ n : ℕ, 4 ≤ n → 2 ∣ n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n h4 hdiv
  -- The only difference from `goldbach` is the parity hypothesis: the target
  -- says `2 ∣ n` where `goldbach` says `Even n`, and `Even a` unfolds to
  -- exactly `2 ∣ a` (`even_iff_two_dvd` is the bridge, definitionally an iff).
  have he : Even n := (even_iff_two_dvd).mpr hdiv
  -- `goldbach` additionally assumes `2 < n`, which is weaker than `4 ≤ n`.
  have h2 : 2 < n := by omega
  exact goldbach n h2 he
