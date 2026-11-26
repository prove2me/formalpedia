-- Prove2me | solution 1 for edenic_semiprime_carmichael_half
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:16.053542+00:00
-- url     : https://prove2.me/submissions/c3d7b38f-5d4e-4138-95f3-4085730db1f2

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ ¬(p + 1 ∣ n - 1) := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  refine ⟨p, hp, hp2, rfl, ?_⟩
  intro hd
  have key : p * (p + 2) + 1 = (p + 1) * (p + 1) := by ring
  have hp1 : p + 1 ∣ p * (p + 2) + 1 := by
    rw [key]
    exact Nat.dvd_mul_right (p + 1) (p + 1)
  have h2 : p + 1 ∣ (p * (p + 2) + 1) - (p * (p + 2) - 1) :=
    Nat.dvd_sub hp1 hd
  have hcalc : (p * (p + 2) + 1) - (p * (p + 2) - 1) = 2 := by
    have h1 : 1 ≤ p * (p + 2) := Nat.succ_le_of_lt (Nat.mul_pos hp.pos hp2.pos)
    omega
  rw [hcalc] at h2
  have hle : p + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  have hne2 : p ≠ 2 := fun h2' => by
    rw [h2'] at hp2
    exact absurd hp2 (by decide)
  have htwo : 2 ≤ p := Nat.Prime.two_le hp
  have hp3 : 3 ≤ p := by omega
  omega

-- #46
