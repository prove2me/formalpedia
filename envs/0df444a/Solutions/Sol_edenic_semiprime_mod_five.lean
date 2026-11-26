-- Prove2me | solution 1 for edenic_semiprime_mod_five
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:38.608201+00:00
-- url     : https://prove2.me/submissions/1d2ec835-6dfc-40d8-ae00-d74482c25d87

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 5 = 3 ∨ n % 5 = 4 ∨ n = 15 ∨ n = 35 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have h5 : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases h5 with h5 | h5 | h5 | h5 | h5
  · obtain ⟨s, rfl⟩ : ∃ s, p = 5 * s := ⟨p / 5, by omega⟩
    have h5d : (5:ℕ) ∣ 5 * s := ⟨s, rfl⟩
    have hp5 : 5 * s = 5 := (Nat.Prime.dvd_iff_eq hp (by decide)).mp h5d
    rw [hp5]
    decide
  · obtain ⟨s, rfl⟩ : ∃ s, p = 5 * s + 1 := ⟨p / 5, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 5 * s + 2 := ⟨p / 5, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 5 * s + 3 := ⟨p / 5, by omega⟩
    have hp2' : 5 * s + 3 + 2 = 5 * (s + 1) := by ring
    rw [hp2'] at hp2
    have h5d : (5:ℕ) ∣ 5 * (s + 1) := ⟨s + 1, rfl⟩
    have hp25 : 5 * (s + 1) = 5 := (Nat.Prime.dvd_iff_eq hp2 (by decide)).mp h5d
    have hs : s = 0 := by omega
    rw [hs]
    decide
  · obtain ⟨s, rfl⟩ : ∃ s, p = 5 * s + 4 := ⟨p / 5, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
