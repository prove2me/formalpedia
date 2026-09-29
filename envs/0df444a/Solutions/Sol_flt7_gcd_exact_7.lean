-- Prove2me | solution 1 for flt7_gcd_exact_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:57:32.911807+00:00
-- url     : https://prove2.me/submissions/93a58960-d607-4d42-b642-a90c0770e8ad

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

private def phi7_wit (a b : ℤ) : ℤ :=
  (a:ℤ)^6 - (a:ℤ)^5*b + (a:ℤ)^4*b^2 - (a:ℤ)^3*b^3 + (a:ℤ)^2*b^4 - a*b^5 + b^6

private lemma apb_dvd_sum7_int (a b : ℕ) :
    ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) := by
  have h : (a:ℤ)+b ∣ (a:ℤ)^7+b^7 := ⟨phi7_wit a b, by unfold phi7_wit; ring⟩
  have h2 : ((a+b:ℕ):ℤ) ∣ ((a^7+b^7:ℕ):ℤ) := by push_cast; exact h
  exact h2

private lemma apb_mul_phi7_nat (a b : ℕ) :
    (a+b) * ((a^7+b^7)/(a+b)) = a^7+b^7 :=
  Nat.mul_div_cancel' (by exact_mod_cast apb_dvd_sum7_int a b)

private lemma phi7_nat_eq_int (a b : ℕ) (hab_ne : a+b ≠ 0) :
    (((a^7+b^7)/(a+b):ℕ):ℤ) = phi7_wit a b := by
  have hprod := apb_mul_phi7_nat a b
  have hab_ne_int : (a:ℤ)+b ≠ 0 := by exact_mod_cast hab_ne
  apply mul_left_cancel₀ hab_ne_int
  have h1 : ((a:ℤ)+b) * (((a^7+b^7)/(a+b):ℕ):ℤ) = (a:ℤ)^7+b^7 := by
    have : (((a+b) * ((a^7+b^7)/(a+b)):ℕ):ℤ) = ((a^7+b^7:ℕ):ℤ) := by exact_mod_cast hprod
    push_cast at this ⊢; linarith
  rw [h1]; unfold phi7_wit; ring

private lemma gcd_dvd_7 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    Nat.gcd (a+b) ((a^7+b^7)/(a+b)) ∣ 7 := by
  have hab_ne : a+b ≠ 0 := by omega
  set g := Nat.gcd (a+b) ((a^7+b^7)/(a+b))
  have hgab : g ∣ a+b := Nat.gcd_dvd_left _ _
  have hgphi : g ∣ (a^7+b^7)/(a+b) := Nat.gcd_dvd_right _ _
  have heq : (((a^7+b^7)/(a+b):ℕ):ℤ) = phi7_wit a b := phi7_nat_eq_int a b hab_ne
  have hg7a6 : g ∣ 7*a^6 := by
    have hq_int : (g:ℤ) ∣ 7*(a:ℤ)^6 := by
      have hgab_int : (g:ℤ) ∣ (a:ℤ)+b := by exact_mod_cast hgab
      have hgphi_int : (g:ℤ) ∣ phi7_wit a b := heq ▸ (by exact_mod_cast hgphi)
      have hident : (a:ℤ)+b ∣ phi7_wit a b - 7*(a:ℤ)^6 :=
        ⟨-6*(a:ℤ)^5+5*(a:ℤ)^4*b-4*(a:ℤ)^3*b^2+3*(a:ℤ)^2*b^3-2*(a:ℤ)*b^4+b^5,
         by unfold phi7_wit; ring⟩
      have h1 : (g:ℤ) ∣ phi7_wit a b - 7*(a:ℤ)^6 := dvd_trans hgab_int hident
      have h2 := dvd_sub hgphi_int h1
      rwa [sub_sub_cancel] at h2
    exact_mod_cast hq_int
  have hcop_apb_a : Nat.Coprime (a+b) a := Nat.coprime_self_add_left.mpr hcop.symm
  have hcop_g_a : Nat.Coprime g a := hcop_apb_a.coprime_dvd_left hgab
  have hcop_g_a6 : Nat.Coprime g (a^6) := hcop_g_a.pow_right 6
  exact hcop_g_a6.dvd_of_dvd_mul_right hg7a6

private lemma seven_dvd_gcd (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) :
    7 ∣ Nat.gcd (a + b) ((a^7 + b^7) / (a + b)) := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply Nat.dvd_gcd h7ab
  set φ := (a^7 + b^7) / (a + b)
  have hab_ne : a + b ≠ 0 := by omega
  have hprod : (a + b) * φ = a^7 + b^7 :=
    Nat.mul_div_cancel' (by exact_mod_cast apb_dvd_sum7_int a b)
  have hφ_ne : φ ≠ 0 := by
    intro h; simp [h] at hprod
    exact absurd hprod (by have : 0 < a^7 := pow_pos ha 7; omega)
  have lte : padicValNat 7 (a ^ 7 + b ^ 7) =
      padicValNat 7 (a + b) + padicValNat 7 7 :=
    padicValNat.pow_add_pow (⟨3, rfl⟩ : Odd 7) h7ab h7a (⟨3, rfl⟩ : Odd 7)
  rw [h_eq, padicValNat.pow c 7] at lte
  have hpc : padicValNat 7 c = 1 := by
    rw [hc, padicValNat.mul (by decide) (by omega),
        padicValNat.self (by decide),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr h7c1))]
  rw [hpc, Nat.mul_one, padicValNat.self (by decide)] at lte
  have hv6 : padicValNat 7 (a + b) = 6 := by omega
  have hprod_val : padicValNat 7 ((a + b) * φ) =
      padicValNat 7 (a + b) + padicValNat 7 φ :=
    padicValNat.mul hab_ne hφ_ne
  have hsum_val : padicValNat 7 (a^7 + b^7) = 7 := by
    rw [h_eq, padicValNat.pow c 7, hpc, Nat.mul_one]
  rw [hprod] at hprod_val; rw [hsum_val, hv6] at hprod_val
  have hφ_val : padicValNat 7 φ = 1 := by omega
  have h71 : 7^1 ∣ φ := (padicValNat_dvd_iff_le hφ_ne).mpr (by linarith)
  simpa using h71

theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1)
    (hcop : Nat.Coprime a b) :
    Nat.gcd (a+b) ((a^7+b^7)/(a+b)) = 7 := by
  have hub := gcd_dvd_7 a b ha hb hcop
  have hlb := seven_dvd_gcd a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  exact Nat.dvd_antisymm hub hlb
