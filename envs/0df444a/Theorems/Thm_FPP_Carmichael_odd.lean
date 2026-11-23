-- Prove2me | Theorems.Thm_FPP_Carmichael_odd
-- name    : FPP.Carmichael.odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:57.758064+00:00
-- url     : https://prove2.me/theorems/8e4d8816-9d6a-4022-87c7-57a4666e9a9e
-- title:
--   Carmichael: odd
-- statement:
--   This is (i) of Thm. 5 of [conrad2016carmichael].
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L61-L68
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L61-L68

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP
open FPP.Carmichael
variable {n : ℕ}

theorem FPP.Carmichael.odd (hn : 2 < n) (hc : Carmichael n) : Odd n := by sorry
