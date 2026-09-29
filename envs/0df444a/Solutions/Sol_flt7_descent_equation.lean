-- Prove2me | solution 1 for flt7_descent_equation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:06:15.595868+00:00
-- url     : https://prove2.me/submissions/bf92e92c-4aaf-44b9-b086-a5969f014524

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
    intro h; simp [h] at hprod
    exact absurd hprod (by have : 0 < a^7 := pow_pos ha 7; omega)
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

theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) :
    ((a+b) / 7^6) * ((a^7+b^7)/(a+b) / 7) = c1^7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hab_ne : a+b ≠ 0 := by omega
  have hv6 : padicValNat 7 (a+b) = 6 := apb_val_eq_6 a b c c1 ha hc_pos h_eq h7a h7ab hc h7c1
  have h_apb_div : 7^6 ∣ a+b := (padicValNat_dvd_iff_le hab_ne).mpr (by linarith)
  have h_phi_div : 7 ∣ (a^7+b^7)/(a+b) :=
    seven_dvd_phi7 a b c c1 ha hb hc_pos h_eq h7a h7ab hc h7c1
  apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 7^7)
  calc 7^7 * (((a+b)/7^6) * ((a^7+b^7)/(a+b)/7))
      = (7^6 * ((a+b)/7^6)) * (7 * ((a^7+b^7)/(a+b)/7)) := by ring
    _ = (a+b) * ((a^7+b^7)/(a+b)) := by
        rw [Nat.mul_div_cancel' h_apb_div, Nat.mul_div_cancel' h_phi_div]
    _ = a^7+b^7 := Nat.mul_div_cancel' (apb_dvd_sum7 a b)
    _ = c^7 := h_eq
    _ = (7*c1)^7 := by rw [hc]
    _ = 7^7 * c1^7 := by ring
