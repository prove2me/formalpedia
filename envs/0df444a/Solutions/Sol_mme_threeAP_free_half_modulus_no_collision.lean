-- Prove2me | solution 1 for mme_threeAP_free_half_modulus_no_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:42:48.863726+00:00
-- url     : https://prove2.me/submissions/e2d72126-1c68-490f-bf30-ca839b07c134

import Mathlib.Data.ZMod.Basic
import Theorems.Thm_mme_3AP_free_no_collision

theorem solution
    (M : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (M / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (a b c : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hmod : (a : ZMod M) + (c : ZMod M) = 2 * (b : ZMod M)) :
    a = b ∧ b = c := by
  have haM : a < M / 2 := Finset.mem_range.mp (hSrange ha)
  have hbM : b < M / 2 := Finset.mem_range.mp (hSrange hb)
  have hcM : c < M / 2 := Finset.mem_range.mp (hSrange hc)
  have hacM : a + c < M := by omega
  have htwobM : 2 * b < M := by omega
  have hnat : a + c = 2 * b := by
    have hcast : ((a + c : ℕ) : ZMod M) = ((2 * b : ℕ) : ZMod M) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod
    exact (ZMod.natCast_eq_natCast_iff (a + c) (2 * b) M).mp hcast
      |>.eq_of_lt_of_lt hacM htwobM
  have hfun := mme_3AP_free_no_collision S hSfree
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (fun _ : Fin 1 => c)
    (fun _ => ha) (fun _ => hb) (fun _ => hc) (fun _ => hnat)
  have hac : a = c := congrFun hfun 0
  constructor <;> omega
