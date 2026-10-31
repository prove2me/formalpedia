-- Prove2me | solution 1 for gpy_mem_primeFactors_lcm
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:36:56.978455+00:00
-- url     : https://prove2.me/submissions/b8565b8c-538a-4118-84e1-b8583a49199c

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

theorem solution {D E p : ℕ} (hD : D ≠ 0) (hE : E ≠ 0) :
    p ∈ (Nat.lcm D E).primeFactors ↔ Nat.Prime p ∧ (p ∣ D ∨ p ∣ E) :=
  mem_primeFactors_lcm_aux hD hE
