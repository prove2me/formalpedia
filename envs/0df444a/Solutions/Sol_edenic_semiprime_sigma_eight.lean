-- Prove2me | solution 1 for edenic_semiprime_sigma_eight
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-25T23:37:47.707903+00:00
-- url     : https://prove2.me/submissions/74c4cb06-1fd3-4791-96aa-b550b23f3ffc

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_sum_divisors

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    (∑ d ∈ n.divisors, d) % 8 = 0 := by
  obtain ⟨p, hp, hp2, rfl, hsum⟩ := edenic_semiprime_sum_divisors _ h
  rw [hsum]
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  have hodd : p % 2 = 1 := by omega
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8
  · obtain ⟨s, rfl⟩ : ∃ s, p = 8 * s + 1 := ⟨p / 8, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 8 * s + 3 := ⟨p / 8, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 8 * s + 5 := ⟨p / 8, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
  · obtain ⟨s, rfl⟩ : ∃ s, p = 8 * s + 7 := ⟨p / 8, by omega⟩
    simp [Nat.mul_mod, Nat.add_mod]
