-- Prove2me | solution 1 for flt7_7_dvd_gcd
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:31:02.65515+00:00
-- url     : https://prove2.me/submissions/b4fdd7c0-7a48-4a35-aa9f-c9f781a50846

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

-- 7 divides gcd(a+b, Phi7_nat) where Phi7_nat = (a^7+b^7)/(a+b).
-- This follows from: 7|(a+b) (given) and v_7(Phi7_nat)=1 (hence 7|Phi7_nat).
theorem solution (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c)
    (h_eq : a ^ 7 + b ^ 7 = c ^ 7)
    (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b)
    (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) :
    7 ∣ Nat.gcd (a + b) ((a^7 + b^7) / (a + b)) := by
  haveI hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply Nat.dvd_gcd h7ab
  set φ := (a^7 + b^7) / (a + b)
  have hab_ne : a + b ≠ 0 := by omega
  have hprod : (a + b) * φ = a^7 + b^7 := by
    apply Nat.mul_div_cancel'
    exact_mod_cast (show ((a + b : ℕ) : ℤ) ∣ ((a^7 + b^7 : ℕ) : ℤ) from by
      push_cast
      exact ⟨(a : ℤ)^6 - (a : ℤ)^5*b + (a : ℤ)^4*b^2 - (a : ℤ)^3*b^3 +
             (a : ℤ)^2*b^4 - a*b^5 + b^6, by ring⟩)
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
