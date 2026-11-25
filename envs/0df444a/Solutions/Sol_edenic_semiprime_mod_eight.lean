-- Prove2me | solution 1 for edenic_semiprime_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T17:35:28.830241+00:00
-- url     : https://prove2.me/submissions/1451c136-3dd8-47ba-b462-a16e8df97bd3

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : n % 8 = 3 ∨ n % 8 = 7 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  subst hk
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · ring_nf
    simp [Nat.mul_mod, Nat.add_mod]
  · ring_nf
    simp [Nat.mul_mod, Nat.add_mod]
