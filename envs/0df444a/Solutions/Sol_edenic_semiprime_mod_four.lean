-- Prove2me | solution 1 for edenic_semiprime_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T06:22:45.359912+00:00
-- url     : https://prove2.me/submissions/fe5c6dc2-dc92-420b-b0d8-11ed9b554d58

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : n % 4 = 3 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  subst hk
  have key : (2 * k + 1) * ((2 * k + 1) + 2) = 4 * k ^ 2 + 8 * k + 3 := by ring
  rw [key]
  simp [Nat.mul_mod, Nat.add_mod]
