-- Prove2me | Theorems.Thm_FPP_orderOf_dvd_sub_one
-- name    : FPP.orderOf_dvd_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:33.690358+00:00
-- url     : https://prove2.me/theorems/20100b97-5bf5-4ae0-a763-34523e6a7871
-- title:
--   FPP: order Of dvd sub one
-- statement:
--   The FPP construction uses the order Of dvd sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L34-L36
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L34-L36

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP

theorem FPP.orderOf_dvd_sub_one {n : ℕ} {a : ZMod n} (h : FPP n a) :
    orderOf a ∣ n - 1 := by sorry
