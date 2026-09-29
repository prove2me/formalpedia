-- Prove2me | solution 1 for fltp_case2_val_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T11:21:28.25112+00:00
-- url     : https://prove2.me/submissions/d7532023-83e6-442b-805d-20ce3fad6203

import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (hc : c ≠ 0) (h_ndvd_a : ¬p ∣ a) (h_dvd_c : p ∣ c) :
    p * padicValNat p c = padicValNat p (a + b) + 1 := by
  -- Step 1: p | a+b (from Fermat's little theorem in ZMod p)
  have h_dvd_apb : p ∣ a + b := by
    rw [← ZMod.natCast_eq_zero_iff (a + b) p]
    push_cast
    have hc0 : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).mpr h_dvd_c
    have heq_mod : (a : ZMod p) ^ p + (b : ZMod p) ^ p = (c : ZMod p) ^ p := by
      have := congr_arg (Nat.cast : ℕ → ZMod p) heq; push_cast at this; exact this
    rw [ZMod.pow_card, ZMod.pow_card, hc0, zero_pow hp.out.pos.ne'] at heq_mod
    exact heq_mod
  -- Step 2: padicValNat p (c^p) = p * padicValNat p c
  have h_val_cp : padicValNat p (c ^ p) = p * padicValNat p c := by
    rw [padicValNat.pow c p]
  -- Step 3: padicValNat p (a^p + b^p) = padicValNat p (a+b) + 1 (LTE)
  have h_lte : padicValNat p (a ^ p + b ^ p) = padicValNat p (a + b) + 1 := by
    have := padicValNat.pow_add_pow h_odd h_dvd_apb h_ndvd_a h_odd
    rw [padicValNat_self] at this; exact this
  -- Step 4: Combine using a^p + b^p = c^p
  rw [heq] at h_lte
  linarith [h_lte.symm.trans h_val_cp]
