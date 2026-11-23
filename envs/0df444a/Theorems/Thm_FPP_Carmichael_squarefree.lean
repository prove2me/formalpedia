-- Prove2me | Theorems.Thm_FPP_Carmichael_squarefree
-- name    : FPP.Carmichael.squarefree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:42.096481+00:00
-- url     : https://prove2.me/theorems/739f0e6f-ee44-4e20-8d2e-fb7ca5c08bf2
-- title:
--   Carmichael: squarefree
-- statement:
--   This is 1st part of the forward direction of Korselt's criterion (Thm. 2 of [conrad2016carmichael]).
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L73-L111
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L73-L111

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

theorem FPP.Carmichael.squarefree [hn : NeZero n] (hc : Carmichael n) :
    Squarefree n := by sorry
