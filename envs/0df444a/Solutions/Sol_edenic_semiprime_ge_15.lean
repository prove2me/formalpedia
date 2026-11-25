-- Prove2me | solution 1 for edenic_semiprime_ge_15
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:27:38.195836+00:00
-- url     : https://prove2.me/submissions/f462202e-1af6-45a3-bc38-513a3f054fd3

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : 15 ≤ n := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · rw [h2] at hp2
      exact absurd hp2 (by decide)
    · obtain ⟨k, hk⟩ := hodd
      have h2le : 2 ≤ p := Nat.Prime.two_le hp
      omega
  nlinarith
