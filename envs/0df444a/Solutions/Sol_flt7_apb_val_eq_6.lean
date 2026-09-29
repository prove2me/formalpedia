-- Prove2me | solution 1 for flt7_apb_val_eq_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:02:03.660541+00:00
-- url     : https://prove2.me/submissions/3956404b-bf78-4ff7-a4f0-662b70d8f1f9

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) :
    padicValNat 7 (a + b) = 6 := by
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
  omega
