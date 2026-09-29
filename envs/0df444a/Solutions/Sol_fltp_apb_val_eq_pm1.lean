-- Prove2me | solution 1 for fltp_apb_val_eq_pm1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:56:17.017626+00:00
-- url     : https://prove2.me/submissions/ea79c082-f98c-475c-ace5-5ad81af92e3a

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

-- For a primitive FLT-p solution (p odd prime) where p | a+b and p | c but p ∤ a, p ∤ c1:
-- The p-adic valuation of (a+b) is exactly p-1.
-- This generalizes the p=7 result flt7_apb_val_eq_6 (where p-1 = 6).
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ)
    (ha : 0 < a) (hc_pos : 0 < c)
    (h_eq : a^p + b^p = c^p) (h_odd : Odd p)
    (hpa : ¬p ∣ a) (hpab : p ∣ a+b) (hc : c = p*c1) (hpc1 : ¬p ∣ c1) :
    padicValNat p (a+b) = p - 1 := by
  have hp_prime : Nat.Prime p := hp.out
  have hc1_pos : 0 < c1 := by
    cases Nat.eq_zero_or_pos c1 with
    | inl h => simp [h, hc] at hc_pos
    | inr h => exact h
  have lte : padicValNat p (a^p + b^p) =
      padicValNat p (a+b) + padicValNat p p :=
    padicValNat.pow_add_pow h_odd hpab hpa h_odd
  rw [h_eq, padicValNat.pow c p] at lte
  have hpc : padicValNat p c = 1 := by
    rw [hc, padicValNat.mul (hp_prime.pos.ne') (hc1_pos.ne'),
        padicValNat.self (hp_prime.one_lt),
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr hpc1))]
  rw [hpc, Nat.mul_one, padicValNat.self (hp_prime.one_lt)] at lte
  omega
