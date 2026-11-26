-- Prove2me | solution 1 for edenic_semiprime_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:34.921476+00:00
-- url     : https://prove2.me/submissions/e4d9224e-2d17-4efe-90f5-c177335f83fe

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 16 = 3 ∨ n % 16 = 15 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  have hodd : p % 2 = 1 := by omega
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · obtain ⟨s, rfl⟩ : ∃ s, p = 4 * s + 1 := ⟨p / 4, by omega⟩
    rw [show (4 * s + 1) * (4 * s + 1 + 2) = 16 * (s * (s + 1)) + 3 from by ring]
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 4 * s + 3 := ⟨p / 4, by omega⟩
    rw [show (4 * s + 3) * (4 * s + 3 + 2) = 16 * (s * (s + 2)) + 15 from by ring]
    simp [Nat.mul_mod, Nat.add_mod]
