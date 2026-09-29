-- Prove2me | solution 1 for flt7_apb_dvd_pow6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T07:47:40.32794+00:00
-- url     : https://prove2.me/submissions/c8e955e2-58c1-4fe5-95d9-7efc893f9869

import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- If a^7+b^7=c^7 with c=7*c1 (7∤c1) and 7∤a and 7|(a+b), then 7^6 | (a+b).
-- Proof uses Lifting the Exponent Lemma (LTE) for p=7.
theorem solution (a b c c1 : ℕ) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b)
    (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) :
    7 ^ 6 ∣ a + b := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
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
  have hab_ne : a + b ≠ 0 := by omega
  rw [padicValNat_dvd_iff_le hab_ne, hv6]
