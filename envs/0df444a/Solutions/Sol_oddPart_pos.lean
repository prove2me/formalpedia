-- Prove2me | solution 1 for oddPart_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:43.526883+00:00
-- url     : https://prove2.me/submissions/c55decad-49f6-46ef-9d0f-e9dcf8c12a3f

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_odd_oddPart

set_option autoImplicit false
open Nat
variable {n : ℕ}
theorem _root_.solution [NeZero n] : 0 < oddPart n := odd_oddPart.pos
