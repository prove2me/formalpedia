-- Prove2me | solution 1 for gpy_primeFactors_lcm_split
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T00:23:41.251972+00:00
-- url     : https://prove2.me/submissions/00a0d948-f6b7-4f2a-89c5-0581885081c9

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem prime_dvd_lcm_aux {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ Nat.lcm m n) :
    p ∣ m ∨ p ∣ n := by
  by_contra hc
  have hc1 : ¬ p ∣ m := fun h => hc (Or.inl h)
  have hc2 : ¬ p ∣ n := fun h => hc (Or.inr h)
  have hcm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc1
  have hcn : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc2
  have hcop : Nat.Coprime p (m * n) := hcm.mul_right hcn
  have hdvd : Nat.lcm m n ∣ m * n :=
    ⟨Nat.gcd m n, (Nat.gcd_mul_lcm m n).symm.trans (mul_comm _ _)⟩
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop) (dvd_trans h hdvd)

theorem mem_primeFactors_lcm_aux {D E p : ℕ} (hD : D ≠ 0) (hE : E ≠ 0) :
    p ∈ (Nat.lcm D E).primeFactors ↔ Nat.Prime p ∧ (p ∣ D ∨ p ∣ E) := by
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpdvd, -⟩
    refine ⟨hp, ?_⟩
    rcases prime_dvd_lcm_aux hp hpdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨hp, h | h⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left D E), Nat.lcm_ne_zero hD hE⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right D E), Nat.lcm_ne_zero hD hE⟩

theorem solution {D E : ℕ} (hD0 : D ≠ 0) (hE0 : E ≠ 0) :
    (Nat.lcm D E).primeFactors
      = (Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors
        ∪ (E / Nat.gcd D E).primeFactors := by
  have hdvdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hdvdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have hD1dvd : D / Nat.gcd D E ∣ D :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdD).symm⟩
  have hE1dvd : E / Nat.gcd D E ∣ E :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdE).symm⟩
  have hgdpos : 0 < Nat.gcd D E :=
    Nat.pos_of_dvd_of_pos hdvdD (Nat.pos_of_ne_zero hD0)
  have hgdne : Nat.gcd D E ≠ 0 := Nat.ne_of_gt hgdpos
  have hD1ne : D / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdD
    rw [h, Nat.zero_mul] at h2
    exact hD0 h2.symm
  have hE1ne : E / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdE
    rw [h, Nat.zero_mul] at h2
    exact hE0 h2.symm
  ext p
  rw [mem_primeFactors_lcm_aux hD0 hE0]
  simp only [Finset.mem_union, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hpp, hpD | hpE⟩
    · have h : p ∣ Nat.gcd D E ∨ p ∣ D / Nat.gcd D E := by
        have hDD : D = Nat.gcd D E * (D / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdD).symm
        rw [hDD] at hpD
        exact hpp.dvd_mul.mp hpD
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inl (Or.inr ⟨hpp, h1, hD1ne⟩)
    · have h : p ∣ Nat.gcd D E ∨ p ∣ E / Nat.gcd D E := by
        have hEE : E = Nat.gcd D E * (E / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdE).symm
        rw [hEE] at hpE
        exact hpp.dvd_mul.mp hpE
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inr ⟨hpp, h1, hE1ne⟩
  · intro hmem
    rcases hmem with hAB | hC
    · rcases hAB with hA | hB
      · exact ⟨hA.1, Or.inl (dvd_trans hA.2.1 hdvdD)⟩
      · exact ⟨hB.1, Or.inl (dvd_trans hB.2.1 hD1dvd)⟩
    · exact ⟨hC.1, Or.inr (dvd_trans hC.2.1 hE1dvd)⟩
