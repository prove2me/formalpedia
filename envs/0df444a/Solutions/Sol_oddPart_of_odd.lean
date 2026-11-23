-- Prove2me | solution 1 for oddPart_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:02.467067+00:00
-- url     : https://prove2.me/submissions/5fe4b098-83c9-418e-a6ae-2989967d6149

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_val__of_odd_644e63334571

set_option autoImplicit false
open Nat
variable {n : ℕ}
theorem _root_.solution (ho : Odd n) : oddPart n = n :=
  by rw [oddPart, val₂_of_odd ho, Nat.pow_zero, Nat.div_one]
