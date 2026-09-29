-- Prove2me | solution 1 for flt7_descent_coprime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:13:17.385105+00:00
-- url     : https://prove2.me/submissions/6bbb19be-00c5-4a90-95d2-99403321b4c3

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

private lemma apb_dvd_sum7 (a b : ℕ) : (a+b) ∣ (a^7+b^7) := by
  have h : (a:ℤ)+b ∣ (a:ℤ)^7+b^7 :=
    ⟨(a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-(a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6, by ring⟩
  have h2 : ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) := by push_cast; exact h
  exact_mod_cast h2

private lemma apb_val_eq_6 (a b c c1 : ℕ) (ha : 0 < a) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    padicValNat 7 (a+b) = 6 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have lte := padicValNat.pow_add_pow (⟨3, rfl⟩ : Odd 7) h7ab h7a (⟨3, rfl⟩ : Odd 7)
  rw [h_eq, padicValNat.pow c 7] at lte
  have hpc : padicValNat 7 c = 1 := by
    rw [hc, padicValNat.mul (by decide) (by omega), padicValNat.self (by decide),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h7c1))]
  rw [hpc, Nat.mul_one, padicValNat.self (by decide)] at lte; omega

private lemma seven_dvd_phi7 (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    7 ∣ (a^7+b^7)/(a+b) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  set φ := (a^7+b^7)/(a+b)
  have hab_ne : a+b ≠ 0 := by omega
  have hprod : (a+b) * φ = a^7+b^7 := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
  have hφ_ne : φ ≠ 0 := by
    intro h; simp [h] at hprod; exact absurd hprod (by have : 0 < a^7 := pow_pos ha 7; omega)
  have lte := padicValNat.pow_add_pow (⟨3, rfl⟩ : Odd 7) h7ab h7a (⟨3, rfl⟩ : Odd 7)
  rw [h_eq, padicValNat.pow c 7] at lte
  have hpc : padicValNat 7 c = 1 := by
    rw [hc, padicValNat.mul (by decide) (by omega), padicValNat.self (by decide),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h7c1))]
  rw [hpc, Nat.mul_one, padicValNat.self (by decide)] at lte
  have hv6 : padicValNat 7 (a+b) = 6 := by omega
  have hprod_val : padicValNat 7 ((a+b) * φ) =
      padicValNat 7 (a+b) + padicValNat 7 φ := padicValNat.mul hab_ne hφ_ne
  rw [hprod] at hprod_val
  have hsum_val : padicValNat 7 (a^7+b^7) = 7 := by
    rw [h_eq, padicValNat.pow c 7, hpc, Nat.mul_one]
  rw [hsum_val, hv6] at hprod_val
  have hφ_val : padicValNat 7 φ = 1 := by omega
  have h71 : 7^1 ∣ φ := (padicValNat_dvd_iff_le hφ_ne).mpr (by linarith)
  simpa using h71

private lemma gcd_exact_7 (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.gcd (a+b) ((a^7+b^7)/(a+b)) = 7 := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  have hub : Nat.gcd (a+b) ((a^7+b^7)/(a+b)) ∣ 7 := by
    set g := Nat.gcd (a+b) ((a^7+b^7)/(a+b))
    have hgab : g ∣ a+b := Nat.gcd_dvd_left _ _
    have hgphi : g ∣ (a^7+b^7)/(a+b) := Nat.gcd_dvd_right _ _
    have heq : (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-
        (a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 := by
      have hprod := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
      have hab_ne_int : (a:ℤ)+b ≠ 0 := by exact_mod_cast hab_ne
      apply mul_left_cancel₀ hab_ne_int
      have h1 : ((a:ℤ)+b) * (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^7+b^7 := by
        have : (((a+b) * ((a^7+b^7)/(a+b)):ℕ):ℤ) = ((a^7+b^7:ℕ):ℤ) := by exact_mod_cast hprod
        push_cast at this ⊢; linarith
      rw [h1]; ring
    have hg7a6 : g ∣ 7*a^6 := by
      have hq_int : (g:ℤ) ∣ 7*(a:ℤ)^6 := by
        have hgab_int : (g:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hgab
        have hgphi_int : (g:ℤ) ∣ (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-
            (a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 := heq ▸ (by exact_mod_cast hgphi)
        have hident : (a:ℤ)+b ∣ (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-
            (a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 - 7*(a:ℤ)^6 :=
          ⟨-6*(a:ℤ)^5+5*(a:ℤ)^4*b-4*(a:ℤ)^3*b^2+3*(a:ℤ)^2*b^3-2*(a:ℤ)*b^4+b^5, by ring⟩
        have h1 : (g:ℤ) ∣ (a:ℤ)^6-(a:ℤ)^5*b+(a:ℤ)^4*b^2-
            (a:ℤ)^3*b^3+(a:ℤ)^2*b^4-a*b^5+b^6 - 7*(a:ℤ)^6 := dvd_trans hgab_int hident
        have h2 := dvd_sub hgphi_int h1
        rwa [sub_sub_cancel] at h2
      exact_mod_cast hq_int
    have hcop_apb_a : Nat.Coprime (a+b) a := Nat.coprime_self_add_left.mpr hcop.symm
    have hcop_g_a : Nat.Coprime g a := hcop_apb_a.coprime_dvd_left hgab
    exact (hcop_g_a.pow_right 6).dvd_of_dvd_mul_right hg7a6
  have hlb : 7 ∣ Nat.gcd (a+b) ((a^7+b^7)/(a+b)) := by
    apply Nat.dvd_gcd h7ab
    exact seven_dvd_phi7 a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  exact Nat.dvd_antisymm hub hlb

theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.Coprime ((a+b) / 7^6) ((a^7+b^7)/(a+b) / 7) := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  set A := (a+b) / 7^6
  set B := (a^7+b^7)/(a+b) / 7
  have hv6 : padicValNat 7 (a+b) = 6 := apb_val_eq_6 a b c c1 ha hc_pos h_eq h7a h7ab hc h7c1
  have h_apb_div : 7^6 ∣ a+b := (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_div : 7 ∣ (a^7+b^7)/(a+b) :=
    seven_dvd_phi7 a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  have hgcd7 : Nat.gcd (a+b) ((a^7+b^7)/(a+b)) = 7 :=
    gcd_exact_7 a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1 hcop
  have h7A : ¬7 ∣ A := by
    simp only [A]
    intro ⟨k, hk⟩
    have hv : 7^7 ∣ a+b := by
      calc 7^7 = 7^6 * 7 := by ring
        _ ∣ 7^6 * ((a+b)/7^6) := by apply Nat.mul_dvd_mul_left; exact ⟨k, hk⟩
        _ = a+b := Nat.mul_div_cancel' h_apb_div
    have : 7 ≤ padicValNat 7 (a+b) := (padicValNat_dvd_iff_le hab_ne).mp hv
    omega
  unfold Nat.Coprime
  set g := Nat.gcd A B
  have hgA : g ∣ A := Nat.gcd_dvd_left _ _
  have hgB : g ∣ B := Nat.gcd_dvd_right _ _
  have hg_apb : g ∣ a+b := (Nat.mul_div_cancel' h_apb_div) ▸ dvd_mul_of_dvd_right hgA (7^6)
  have hg_phi : g ∣ (a^7+b^7)/(a+b) :=
    (Nat.mul_div_cancel' h_phi_div) ▸ dvd_mul_of_dvd_right hgB 7
  have hg7 : g ∣ 7 := hgcd7 ▸ Nat.dvd_gcd hg_apb hg_phi
  have hg_ne7 : g ≠ 7 := fun hg => h7A (hg ▸ hgA)
  rcases (by decide : Nat.Prime 7).eq_one_or_self_of_dvd g hg7 with h1 | h7
  · exact h1
  · exact absurd h7 hg_ne7
