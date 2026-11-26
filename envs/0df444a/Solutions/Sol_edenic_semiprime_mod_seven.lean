-- Prove2me | solution 1 for edenic_semiprime_mod_seven
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:40.874846+00:00
-- url     : https://prove2.me/submissions/ccc13a5b-1712-4d95-ba38-814f412d11fe

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 7 = 1 ∨ n % 7 = 3 ∨ n % 7 = 6 ∨ n = 35 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have h7 : p % 7 = 0 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 3 ∨ p % 7 = 4 ∨ p % 7 = 5 ∨
      p % 7 = 6 := by omega
  rcases h7 with h7 | h7 | h7 | h7 | h7 | h7 | h7
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s := ⟨p / 7, by omega⟩
    have h7d : (7:ℕ) ∣ 7 * s := ⟨s, rfl⟩
    have hp7 : 7 * s = 7 := (Nat.Prime.dvd_iff_eq hp (by decide)).mp h7d
    rw [hp7] at hp2
    exact absurd hp2 (by decide)
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 1 := ⟨p / 7, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 2 := ⟨p / 7, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 3 := ⟨p / 7, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 4 := ⟨p / 7, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 5 := ⟨p / 7, by omega⟩
    have hp2' : 7 * s + 5 + 2 = 7 * (s + 1) := by ring
    rw [hp2'] at hp2
    have h7d : (7:ℕ) ∣ 7 * (s + 1) := ⟨s + 1, rfl⟩
    have hp27 : 7 * (s + 1) = 7 := (Nat.Prime.dvd_iff_eq hp2 (by decide)).mp h7d
    have hs : s = 0 := by omega
    rw [hs]
    decide
  · obtain ⟨s, rfl⟩ : ∃ s, p = 7 * s + 6 := ⟨p / 7, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
