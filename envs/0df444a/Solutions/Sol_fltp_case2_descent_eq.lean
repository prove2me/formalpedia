-- Prove2me | solution 1 for fltp_case2_descent_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T00:57:05.81068+00:00
-- url     : https://prove2.me/submissions/1b4cf4be-b8b9-4f9b-9413-fe7ca6c0b610

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity

-- In FLT Case 2 (p odd prime, a^p+b^p=c^p, c=p*c1, p∤a, p∤c1, p|a+b):
-- The descent equation: ((a+b)/p^(p-1)) * ((a^p+b^p)/(a+b)/p) = c1^p.
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (ha : 0 < a) (hb : 0 < b)
    (h_ndvd_a : ¬p ∣ a) (hpab : p ∣ a + b)
    (hc : c = p * c1) (h_ndvd_c1 : ¬p ∣ c1) :
    (a + b) / p ^ (p - 1) * ((a ^ p + b ^ p) / (a + b) / p) = c1 ^ p := by
  have hp_prime : Nat.Prime p := hp.out
  have hp_ne : p ≠ 0 := hp_prime.pos.ne'
  have hp_ge : 2 ≤ p := hp_prime.two_le
  have hc1_pos : 0 < c1 := by
    rcases Nat.eq_zero_or_pos c1 with h | h
    · exact absurd (h ▸ dvd_zero p) h_ndvd_c1
    · exact h
  have hc_pos : 0 < c := hc ▸ Nat.mul_pos hp_prime.pos hc1_pos
  have hab_ne : a + b ≠ 0 := by omega
  have h_apb_dvd : (a + b) ∣ (a ^ p + b ^ p) := by
    have h_int : (a : ℤ) + b ∣ (a : ℤ) ^ p + b ^ p := by
      have h1 : (a : ℤ) - (-b) ∣ (a : ℤ) ^ p - (-b) ^ p := sub_dvd_pow_sub_pow _ _ _
      rw [h_odd.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at h1; exact h1
    exact_mod_cast (show ((a + b : ℕ) : ℤ) ∣ ((a ^ p + b ^ p : ℕ) : ℤ) by push_cast; exact h_int)
  have hpc : padicValNat p c = 1 := by
    rw [hc, padicValNat.mul hp_ne hc1_pos.ne',
        padicValNat.self hp_prime.one_lt,
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h_ndvd_c1))]
  have h_lte : padicValNat p (a ^ p + b ^ p) =
      padicValNat p (a + b) + padicValNat p p :=
    padicValNat.pow_add_pow h_odd hpab h_ndvd_a h_odd
  have h_sum_val : padicValNat p (a ^ p + b ^ p) = p := by
    rw [heq, padicValNat.pow c p, hpc, Nat.mul_one]
  have h_apb_val : padicValNat p (a + b) = p - 1 := by
    rw [padicValNat.self hp_prime.one_lt] at h_lte
    omega
  have h_apb_div : p ^ (p - 1) ∣ a + b :=
    (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_ne : (a ^ p + b ^ p) / (a + b) ≠ 0 := by
    intro h
    have := Nat.mul_div_cancel' h_apb_dvd
    rw [h, Nat.mul_zero] at this
    have : 0 < a ^ p := pow_pos ha p
    omega
  have h_phi_val : padicValNat p ((a ^ p + b ^ p) / (a + b)) = 1 := by
    have prod_val : padicValNat p ((a + b) * ((a ^ p + b ^ p) / (a + b))) =
        padicValNat p (a + b) + padicValNat p ((a ^ p + b ^ p) / (a + b)) :=
      padicValNat.mul hab_ne h_phi_ne
    rw [Nat.mul_div_cancel' h_apb_dvd, h_sum_val, h_apb_val] at prod_val
    omega
  have h_phi_div : p ∣ (a ^ p + b ^ p) / (a + b) := by
    have h1 : p ^ 1 ∣ (a ^ p + b ^ p) / (a + b) :=
      (padicValNat_dvd_iff_le h_phi_ne).mpr (by linarith)
    simpa using h1
  have hpp : p ^ (p - 1) * p = p ^ p := by
    rw [← pow_succ]; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hp_prime.pos p)
  calc p ^ p * ((a + b) / p ^ (p - 1) * ((a ^ p + b ^ p) / (a + b) / p))
      = p ^ (p - 1) * ((a + b) / p ^ (p - 1)) * (p * ((a ^ p + b ^ p) / (a + b) / p)) := by
          rw [← hpp]; ring
    _ = (a + b) * ((a ^ p + b ^ p) / (a + b)) := by
          rw [Nat.mul_div_cancel' h_apb_div, Nat.mul_div_cancel' h_phi_div]
    _ = a ^ p + b ^ p := Nat.mul_div_cancel' h_apb_dvd
    _ = c ^ p := heq
    _ = (p * c1) ^ p := by rw [hc]
    _ = p ^ p * c1 ^ p := mul_pow p c1 p
