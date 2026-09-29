-- Prove2me | solution 1 for flt7_phi7_val_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:27:54.857085+00:00
-- url     : https://prove2.me/submissions/bb0d93d9-44d5-428c-8b82-2c326ba9593b

import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- padicValNat 7 of Phi7_nat = 1 in the FLT-7 setting.
-- Here Phi7_nat := (a^7+b^7)/(a+b) (the exact integer quotient).
-- Given: a^7+b^7=c^7, c=7*c1 (7∤c1), 7∤a, 7|a+b, a,b,c>0.
-- Proof: v_7(a^7+b^7)=7, v_7(a+b)=6, multiplicativity gives v_7(Phi7)=1.
theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b)
    (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) :
    padicValNat 7 ((a^7 + b^7) / (a + b)) = 1 := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  set φ := (a^7 + b^7) / (a + b)
  have hab_ne : a + b ≠ 0 := by omega
  -- (a+b) * φ = a^7+b^7 (exact division)
  have hprod : (a + b) * φ = a^7 + b^7 := by
    apply Nat.mul_div_cancel'
    have h : (a : ℤ) + b ∣ (a : ℤ)^7 + (b : ℤ)^7 :=
      ⟨(a : ℤ)^6 - (a : ℤ)^5*(b : ℤ) + (a : ℤ)^4*(b : ℤ)^2 -
       (a : ℤ)^3*(b : ℤ)^3 + (a : ℤ)^2*(b : ℤ)^4 - (a : ℤ)*(b : ℤ)^5 + (b : ℤ)^6,
       by ring⟩
    exact_mod_cast (show ((a + b : ℕ) : ℤ) ∣ ((a^7 + b^7 : ℕ) : ℤ) from by push_cast; exact h)
  -- φ ≠ 0
  have hφ_ne : φ ≠ 0 := by
    intro h; simp [h] at hprod
    exact absurd hprod (by have : 0 < a^7 := pow_pos ha 7; omega)
  -- LTE: v_7(a^7+b^7) = v_7(a+b) + 1
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
  -- v_7((a+b)*φ) = v_7(a+b) + v_7(φ) = 7
  have hprod_val : padicValNat 7 ((a + b) * φ) =
      padicValNat 7 (a + b) + padicValNat 7 φ :=
    padicValNat.mul hab_ne hφ_ne
  have hsum_val : padicValNat 7 (a^7 + b^7) = 7 := by
    rw [h_eq, padicValNat.pow c 7, hpc, Nat.mul_one]
  rw [hprod] at hprod_val
  rw [hsum_val, hv6] at hprod_val
  omega
