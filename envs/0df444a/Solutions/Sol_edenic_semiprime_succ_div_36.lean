-- Prove2me | solution 1 for edenic_semiprime_succ_div_36
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:20.496801+00:00
-- url     : https://prove2.me/submissions/5597de64-b819-4dd7-9949-5db416216255

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    (n + 1 ∣ 36) ↔ n = 35 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  have htwo : 2 ≤ p := Nat.Prime.two_le hp
  have hp3 : 3 ≤ p := by omega
  constructor
  · intro hd
    have key : p * (p + 2) + 1 = (p + 1) * (p + 1) := by ring
    rw [key] at hd
    have hsq : (p + 1) * (p + 1) ≤ 36 := Nat.le_of_dvd (by norm_num) hd
    have hle : p + 1 ≤ 6 := by nlinarith
    have h35 : p = 3 ∨ p = 4 ∨ p = 5 := by omega
    rcases h35 with (rfl | rfl | rfl)
    · exact absurd hd (by norm_num)
    · exact absurd hd (by norm_num)
    · rfl
  · intro h
    norm_num [h]

-- #41
