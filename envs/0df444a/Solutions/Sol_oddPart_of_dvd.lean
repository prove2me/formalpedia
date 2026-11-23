-- Prove2me | solution 1 for oddPart_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:44.034316+00:00
-- url     : https://prove2.me/submissions/67d97dad-7a74-4968-b560-e1ae371dc8b3

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_two_pow_val__mul_oddPart_d784ed0aab74
import Theorems.Thm_odd_oddPart

set_option autoImplicit false
open Nat
variable {n : ℕ}
variable {m : ℕ}
theorem _root_.solution [NeZero m] (h : m ∣ n) : oddPart m ∣ oddPart n := by
  rw [← two_pow_val₂_mul_oddPart m, ← two_pow_val₂_mul_oddPart n] at h
  apply ((prime_two.coprime_iff_not_dvd.mpr _).pow_left _).symm.dvd_mul_left.mp
    (dvd_of_mul_left_dvd h)
  rw [← even_iff_two_dvd, not_even_iff_odd]
  exact odd_oddPart
