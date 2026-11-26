-- Prove2me | solution 1 for edenic_semiprime_not_perfect
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:25.004279+00:00
-- url     : https://prove2.me/submissions/5f5a7f55-3d9a-4c00-8544-94b6357f6c5f

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) : ¬ Nat.Perfect n := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  intro hperf
  have h0 : 0 < p * (p + 2) := Nat.mul_pos hp.pos hp2.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul h0] at hperf
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  have htwo : 2 ≤ p := Nat.Prime.two_le hp
  have hp3 : 3 ≤ p := by omega
  have hs1 : ∑ i ∈ p.divisors, i = 1 + p := by
    rw [Nat.Prime.divisors hp, Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.sum_singleton]
  have hs2 : ∑ i ∈ (p + 2).divisors, i = 1 + (p + 2) := by
    rw [Nat.Prime.divisors hp2, Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.sum_singleton]
  have hs : ∑ i ∈ (p * (p + 2)).divisors, i = (1 + p) * (1 + (p + 2)) := by
    rw [Nat.Coprime.sum_divisors_mul (twin_primes_coprime p hp hp2), hs1, hs2]
  rw [hs] at hperf
  have hkey : (1 + p) * (1 + (p + 2)) = p * p + 4 * p + 3 := by ring
  have hkey2 : 2 * (p * (p + 2)) = 2 * (p * p) + 4 * p := by ring
  rw [hkey, hkey2] at hperf
  have hge : 3 * 3 ≤ p * p := Nat.mul_le_mul hp3 hp3
  omega

-- #45
