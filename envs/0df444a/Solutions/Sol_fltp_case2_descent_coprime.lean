-- Prove2me | solution 1 for fltp_case2_descent_coprime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T00:57:10.688712+00:00
-- url     : https://prove2.me/submissions/d021d023-3a9a-4801-9b29-dc0c96e30b96

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

-- In FLT Case 2 (p odd prime, a^p+b^p=c^p, c=p*c1, p∤a, p∤c1, p|a+b, gcd(a,b)=1):
-- The descent factors (a+b)/p^(p-1) and Phi_p/p are coprime.
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (ha : 0 < a) (hb : 0 < b)
    (h_ndvd_a : ¬p ∣ a) (hpab : p ∣ a + b)
    (hc : c = p * c1) (h_ndvd_c1 : ¬p ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.Coprime ((a + b) / p ^ (p - 1)) ((a ^ p + b ^ p) / (a + b) / p) := by
  have hp_prime : Nat.Prime p := hp.out
  have hp_ne : p ≠ 0 := hp_prime.pos.ne'
  have hc1_pos : 0 < c1 := by
    rcases Nat.eq_zero_or_pos c1 with h | h
    · exact absurd (h ▸ dvd_zero p) h_ndvd_c1
    · exact h
  have hc_pos : 0 < c := hc ▸ Nat.mul_pos hp_prime.pos hc1_pos
  have hab_ne : a + b ≠ 0 := by omega
  have h_apb_dvd : (a + b) ∣ (a ^ p + b ^ p) := by
    have : (a : ℤ) + b ∣ (a : ℤ) ^ p + b ^ p := by
      have h1 : (a : ℤ) - (-b) ∣ (a : ℤ) ^ p - (-b) ^ p := sub_dvd_pow_sub_pow _ _ _
      rw [h_odd.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at h1; exact h1
    exact_mod_cast (show ((a + b : ℕ) : ℤ) ∣ ((a ^ p + b ^ p : ℕ) : ℤ) by push_cast; exact this)
  have hpc : padicValNat p c = 1 := by
    rw [hc, padicValNat.mul hp_ne hc1_pos.ne',
        padicValNat.self hp_prime.one_lt,
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h_ndvd_c1))]
  have h_sum_val : padicValNat p (a ^ p + b ^ p) = p := by
    rw [heq, padicValNat.pow c p, hpc, Nat.mul_one]
  have h_apb_val : padicValNat p (a + b) = p - 1 := by
    have lte := padicValNat.pow_add_pow h_odd hpab h_ndvd_a h_odd
    rw [padicValNat.self hp_prime.one_lt] at lte; omega
  have h_apb_div : p ^ (p - 1) ∣ a + b :=
    (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_ne : (a ^ p + b ^ p) / (a + b) ≠ 0 := by
    intro h; have := Nat.mul_div_cancel' h_apb_dvd
    rw [h, Nat.mul_zero] at this; exact absurd this (by have : 0 < a ^ p := pow_pos ha p; omega)
  have h_phi_val : padicValNat p ((a ^ p + b ^ p) / (a + b)) = 1 := by
    have prod_val : padicValNat p ((a + b) * ((a ^ p + b ^ p) / (a + b))) =
        padicValNat p (a + b) + padicValNat p ((a ^ p + b ^ p) / (a + b)) :=
      padicValNat.mul hab_ne h_phi_ne
    rw [Nat.mul_div_cancel' h_apb_dvd, h_sum_val, h_apb_val] at prod_val; omega
  have h_phi_div : p ∣ (a ^ p + b ^ p) / (a + b) := by
    have h1 : p ^ 1 ∣ (a ^ p + b ^ p) / (a + b) :=
      (padicValNat_dvd_iff_le h_phi_ne).mpr (by linarith)
    simpa using h1
  set A := (a + b) / p ^ (p - 1)
  set B := (a ^ p + b ^ p) / (a + b) / p
  have h_A_ne : A ≠ 0 := by
    simp only [A]; intro h; have := Nat.mul_div_cancel' h_apb_div
    rw [h, Nat.mul_zero] at this; omega
  have h_p_ndvd_A : ¬p ∣ A := by
    simp only [A]; intro ⟨k, hk⟩
    have hv : p ^ p ∣ a + b := by
      calc p ^ p = p ^ (p - 1) * p := by rw [← pow_succ]; congr 1; omega
        _ ∣ p ^ (p - 1) * A := Nat.mul_dvd_mul_left _ ⟨k, hk⟩
        _ = a + b := Nat.mul_div_cancel' h_apb_div
    have hbad := (padicValNat_dvd_iff_le hab_ne).mp hv
    rw [h_apb_val] at hbad; omega
  unfold Nat.Coprime
  set g := Nat.gcd A B
  have hg_pos : 0 < g := by
    rw [Nat.pos_iff_ne_zero]; intro h
    exact h_A_ne ((Nat.gcd_eq_zero_iff.mp h).1)
  suffices g ≤ 1 by omega
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq_prime, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
  have hqA : q ∣ A := hqdvd.trans (Nat.gcd_dvd_left A B)
  have hqB : q ∣ B := hqdvd.trans (Nat.gcd_dvd_right A B)
  have hq_apb : q ∣ a + b :=
    (Nat.mul_div_cancel' h_apb_div) ▸ dvd_mul_of_dvd_right hqA (p ^ (p - 1))
  by_cases hq_eq_p : q = p
  · exact h_p_ndvd_A (hq_eq_p ▸ hqA)
  · have hq_ndvd_a : ¬q ∣ a := by
      intro hqa
      have hqb : q ∣ b := (Nat.dvd_add_right hqa).mp hq_apb
      exact hq_prime.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hqa hqb))
    have hq_ndvd_p : ¬q ∣ p := by
      intro hqp
      rcases hp_prime.eq_one_or_self_of_dvd q hqp with h1 | h2
      · exact hq_prime.one_lt.ne' h1
      · exact hq_eq_p h2
    have hq_phi : q ∣ (a ^ p + b ^ p) / (a + b) :=
      (Nat.mul_div_cancel' h_phi_div) ▸ dvd_mul_of_dvd_right hqB p
    have h_geom : (↑a + ↑b : ℤ) * ∑ i ∈ Finset.range p, (↑a : ℤ) ^ i * (-↑b) ^ (p - 1 - i) =
        (↑a : ℤ) ^ p + ↑b ^ p := by
      have h := (Commute.all (↑a : ℤ) (-↑b)).geom_sum₂_mul p
      rw [show (↑a : ℤ) - -↑b = ↑a + ↑b from by ring,
          h_odd.neg_pow (↑b : ℤ), sub_neg_eq_add, mul_comm] at h
      exact h
    have h_phi_cast : (↑((a ^ p + b ^ p) / (a + b)) : ℤ) =
        ∑ i ∈ Finset.range p, (↑a : ℤ) ^ i * (-↑b) ^ (p - 1 - i) := by
      apply mul_left_cancel₀ (show (↑(a + b) : ℤ) ≠ 0 from by exact_mod_cast hab_ne)
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h_apb_dvd]
      push_cast; linarith [h_geom]
    have h_cong : (↑a + ↑b : ℤ) ∣ (↑((a ^ p + b ^ p) / (a + b)) : ℤ) - ↑p * ↑a ^ (p - 1) := by
      rw [h_phi_cast]
      rw [show ∑ i ∈ Finset.range p, (↑a : ℤ) ^ i * (-↑b) ^ (p - 1 - i) - ↑p * ↑a ^ (p - 1) =
          ∑ i ∈ Finset.range p, ((↑a : ℤ) ^ i * (-↑b) ^ (p - 1 - i) - ↑a ^ (p - 1)) from by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
      apply Finset.dvd_sum
      intro i hi
      have hle : i ≤ p - 1 := by have := Finset.mem_range.mp hi; omega
      have h_neg_diff : (↑a + ↑b : ℤ) ∣ (-↑b : ℤ) ^ (p - 1 - i) - ↑a ^ (p - 1 - i) := by
        have h0 := sub_dvd_pow_sub_pow (-↑b : ℤ) (↑a : ℤ) (p - 1 - i)
        rwa [show (-↑b : ℤ) - ↑a = -(↑a + ↑b) from by ring, neg_dvd] at h0
      have hpow_eq : (↑a : ℤ) ^ i * ↑a ^ (p - 1 - i) = ↑a ^ (p - 1) := by
        rw [← pow_add]; congr 1; omega
      calc (↑a + ↑b : ℤ)
          ∣ ↑a ^ i * ((-↑b) ^ (p - 1 - i) - ↑a ^ (p - 1 - i)) :=
              dvd_mul_of_dvd_right h_neg_diff _
        _ = ↑a ^ i * (-↑b) ^ (p - 1 - i) - ↑a ^ i * ↑a ^ (p - 1 - i) := by ring
        _ = ↑a ^ i * (-↑b) ^ (p - 1 - i) - ↑a ^ (p - 1) := by rw [hpow_eq]
    have hq_apb_int : (↑q : ℤ) ∣ ↑a + ↑b := by exact_mod_cast hq_apb
    have hq_phi_int : (↑q : ℤ) ∣ ↑((a ^ p + b ^ p) / (a + b)) := by exact_mod_cast hq_phi
    have hq_pa : (↑q : ℤ) ∣ ↑p * ↑a ^ (p - 1) := by
      have hq_cong : (↑q : ℤ) ∣ ↑((a ^ p + b ^ p) / (a + b)) - ↑p * ↑a ^ (p - 1) :=
        hq_apb_int.trans h_cong
      have h := dvd_sub hq_phi_int hq_cong
      simp only [sub_sub_cancel] at h
      exact h
    have hq_dvd_p : q ∣ p := by
      have : q ∣ p * a ^ (p - 1) := by exact_mod_cast hq_pa
      rcases hq_prime.dvd_mul.mp this with h | h
      · exact h
      · exact absurd (hq_prime.dvd_of_dvd_pow h) hq_ndvd_a
    exact hq_ndvd_p hq_dvd_p
