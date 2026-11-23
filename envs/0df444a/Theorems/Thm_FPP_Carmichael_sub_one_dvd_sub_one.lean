-- Prove2me | Theorems.Thm_FPP_Carmichael_sub_one_dvd_sub_one
-- name    : FPP.Carmichael.sub_one_dvd_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:44.621722+00:00
-- url     : https://prove2.me/theorems/522e2caa-7bd4-4266-b6e6-3b8ad81d470b
-- title:
--   Carmichael: sub one dvd sub one
-- statement:
--   This is 2nd part of the forward direction of Korselt's criterion (Thm. 2 of [conrad2016carmichael]).
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L116-L125
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L116-L125

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

theorem FPP.Carmichael.sub_one_dvd_sub_one {p : ℕ} [NeZero n] [Fact p.Prime] (hc : Carmichael n)
    (hp : p ∣ n) : p - 1 ∣ n - 1 := by sorry
