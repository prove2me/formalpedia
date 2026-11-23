-- Prove2me | Theorems.Thm_FPP_of_prime
-- name    : FPP.of_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:42.687428+00:00
-- url     : https://prove2.me/theorems/76610b2d-a66e-42fb-adc5-6988fb2b0a79
-- title:
--   FPP: of prime
-- statement:
--   A prime is a Fermat probable prime to any nonzero base.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L28-L30
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L28-L30

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP

theorem FPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    FPP p a := by sorry
