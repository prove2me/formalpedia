-- Prove2me | solution 1 for fltp_residue_constraint
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:02:24.759288+00:00
-- url     : https://prove2.me/submissions/58e29978-5c66-4b9f-bdd2-86945311cb95

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic

private lemma fltp_fermat_little (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℤ) : (p : ℤ) ∣ a^p - a := by
  have hmod : ∀ x : ZMod p, x^p = x := fun x => by
    have h := FiniteField.pow_card (K := ZMod p) x
    rwa [ZMod.card p] at h
  have h2 : ((a^p - a : ℤ) : ZMod p) = 0 := by push_cast; rw [hmod]; exact sub_self _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a^p - a) p).mp h2

-- For any prime p and integers a, b, c with a^p+b^p=c^p, p divides a+b-c.
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℤ)
    (h_eq : a^p+b^p = c^p) : (p:ℤ) ∣ a+b-c := by
  have ha := fltp_fermat_little p a
  have hb := fltp_fermat_little p b
  have hc := fltp_fermat_little p c
  have h1 : (p:ℤ) ∣ (a^p-a) + (b^p-b) - (c^p-c) := dvd_sub (dvd_add ha hb) hc
  have key : (a^p-a) + (b^p-b) - (c^p-c) = -(a+b-c) := by
    have h0 : a^p+b^p-c^p = 0 := by omega
    omega
  rw [key] at h1
  exact dvd_neg.mp h1
