-- Prove2me | solution 1 for edenic_semiprime_five_dvd
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:22:57.982704+00:00
-- url     : https://prove2.me/submissions/23445768-decd-417a-89a1-854bc105d5e1

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    5 ∣ n ↔ n = 15 ∨ n = 35 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  constructor
  · intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hdvd with h5 | h5
    · rcases (Nat.dvd_prime hp).mp h5 with habs | heq
      · exact absurd habs (by decide)
      · subst heq
        right
        rfl
    · rcases (Nat.dvd_prime hp2).mp h5 with habs | heq
      · exact absurd habs (by decide)
      · have hp3 : p = 3 := by omega
        subst hp3
        left
        rfl
  · rintro (h15 | h35)
    · rw [h15]
      decide
    · rw [h35]
      decide
