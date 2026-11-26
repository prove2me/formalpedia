-- Prove2me | solution 1 for edenic_semiprime_hypotenuse
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T11:34:00.499983+00:00
-- url     : https://prove2.me/submissions/4fe8c066-fda4-4e8d-a883-ae09faec7ab3

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = n ^ 2 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have hne2 : p ≠ 2 := fun h2 => by
    rw [h2] at hp2
    exact absurd hp2 (by decide)
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hne2
  have hodd : p % 2 = 1 := by omega
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  -- q is the twin prime congruent to 1 mod 4
  have hex : ∃ q m, q.Prime ∧ m.Prime ∧ p * (p + 2) = q * m ∧ q % 4 = 1 := by
    rcases h4 with h4 | h4
    · exact ⟨p, p + 2, hp, hp2, rfl, h4⟩
    · exact ⟨p + 2, p, hp2, hp, by ring, by omega⟩
  obtain ⟨q, m, hq, hm, hnm, hq4⟩ := hex
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a0, b0, h0⟩ := Nat.Prime.sq_add_sq (by omega : q % 4 ≠ 3)
  -- both summands are nonzero: q is prime
  have ha00 : a0 ≠ 0 := by
    rintro rfl
    simp [pow_two] at h0
    by_cases hb : b0 = 1
    · subst hb; simp at h0; exact absurd h0.symm hq.ne_one
    · have hnb : ¬(b0 * b0).Prime := Nat.not_prime_mul hb hb
      rw [h0] at hnb
      exact absurd hq hnb
  have hb00 : b0 ≠ 0 := by
    rintro rfl
    simp [pow_two] at h0
    by_cases ha : a0 = 1
    · subst ha; simp at h0; exact absurd h0.symm hq.ne_one
    · have hnb : ¬(a0 * a0).Prime := Nat.not_prime_mul ha ha
      rw [h0] at hnb
      exact absurd hq hnb
  -- and they differ: q is odd
  have hne0 : a0 ≠ b0 := by
    rintro rfl
    rw [← two_mul] at h0
    have h2q : 2 ∣ q := ⟨a0 ^ 2, by rw [← h0]⟩
    rcases (Nat.dvd_prime hq).mp h2q with h | h
    · omega
    · omega
  -- normalize so b ≤ a (the sum of two squares is symmetric)
  obtain ⟨a, b, hab, hba, ha0, hb0, hne⟩ :
      ∃ a b, a ^ 2 + b ^ 2 = q ∧ b ≤ a ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
    rcases le_total b0 a0 with h | h
    · exact ⟨a0, b0, h0, h, ha00, hb00, hne0⟩
    · exact ⟨b0, a0, by rwa [add_comm] at h0, h, hb00, ha00, fun he => hne0 he.symm⟩
  have hlt : b < a := lt_of_le_of_ne hba fun h => hne h.symm
  have hblt : b ^ 2 < a ^ 2 := by
    simp only [pow_two]
    exact mul_self_lt_mul_self (by omega : 0 ≤ b) hlt
  -- q^2 = (a^2 - b^2)^2 + (2ab)^2 (Brahmagupta, transported through ℤ)
  have hsq : q * q = (a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2 := by
    have hqz : ((q : ℤ)) * q = (((a ^ 2 - b ^ 2 : ℕ) : ℤ)) ^ 2 + (((2 * a * b : ℕ) : ℤ)) ^ 2 := by
      have hcq : (q : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab.symm
      have hsub : (((a ^ 2 - b ^ 2 : ℕ) : ℤ)) = (a : ℤ) ^ 2 - (b : ℤ) ^ 2 :=
        Int.ofNat_sub hblt.le
      simp only [hcq, hsub]
      push_cast
      ring
    exact_mod_cast hqz
  have hm0 : 0 < m := by
    have hm2 : 2 ≤ m := hm.two_le
    omega
  have hleg1 : 0 < a ^ 2 - b ^ 2 := Nat.sub_pos_of_lt hblt
  have hleg2 : 0 < 2 * a * b := by positivity
  have hfin : ((a ^ 2 - b ^ 2) * m) ^ 2 + (2 * a * b * m) ^ 2 = (q * m) ^ 2 := by
    calc ((a ^ 2 - b ^ 2) * m) ^ 2 + (2 * a * b * m) ^ 2
        = ((a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2) * (m ^ 2) := by ring
      _ = (q * q) * (m ^ 2) := by rw [← hsq]
      _ = (q * m) ^ 2 := by ring
  refine ⟨(a ^ 2 - b ^ 2) * m, 2 * a * b * m, Nat.mul_pos hleg1 hm0,
    Nat.mul_pos hleg2 hm0, ?_⟩
  rw [hnm, hfin]
