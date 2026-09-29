-- Prove2me | solution 1 for flt7_residue_constraint
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T09:51:49.08803+00:00
-- url     : https://prove2.me/submissions/c7996ee3-cfe9-450f-be82-3c56b66ff37b

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic

private lemma flt7_fermat_little (a : ℤ) : (7 : ℤ) ∣ a^7 - a := by
  have hmod : ∀ x : ZMod 7, x^7 = x := by decide
  have h2 : ((a^7 - a : ℤ) : ZMod 7) = 0 := by
    push_cast; rw [hmod]; exact sub_self _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a^7 - a) 7).mp h2

-- For any FLT-7 equation a^7+b^7=c^7 over ℤ, we have 7 | a+b-c.
-- Proof: by Fermat's Little Theorem, a^7 ≡ a, b^7 ≡ b, c^7 ≡ c (mod 7),
-- so a+b ≡ a^7+b^7 = c^7 ≡ c (mod 7).
theorem solution (a b c : ℤ) (h_eq : a^7+b^7 = c^7) : (7:ℤ) ∣ a+b-c := by
  have ha := flt7_fermat_little a
  have hb := flt7_fermat_little b
  have hc := flt7_fermat_little c
  have h1 : (7:ℤ) ∣ (a^7-a) + (b^7-b) - (c^7-c) := dvd_sub (dvd_add ha hb) hc
  have key : (a^7-a) + (b^7-b) - (c^7-c) = -(a+b-c) := by
    have h0 : a^7+b^7-c^7 = 0 := by omega
    omega
  rw [key] at h1
  exact dvd_neg.mp h1
