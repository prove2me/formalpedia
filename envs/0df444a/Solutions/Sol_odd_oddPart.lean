-- Prove2me | solution 1 for odd_oddPart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:08.130448+00:00
-- url     : https://prove2.me/submissions/d41235d8-c6bd-47dc-bbe6-ead415ba933d

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74

set_option autoImplicit false
open Nat
variable {n : ℕ}
theorem _root_.solution [hn : NeZero n] : Odd (oddPart n) := by
  have h := pow_succ_padicValNat_not_dvd (p := 2) hn.out
  contrapose! h
  rw [not_odd_iff] at h
  rw [Nat.pow_succ, ← val₂]
  have h' := mul_dvd_mul_left (2 ^ val₂ n) (dvd_of_mod_eq_zero h)
  rwa [two_pow_val₂_mul_oddPart] at h'
