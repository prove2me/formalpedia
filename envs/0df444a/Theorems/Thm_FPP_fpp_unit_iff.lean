-- Prove2me | Theorems.Thm_FPP_fpp_unit_iff
-- name    : FPP.fpp_unit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:41.619001+00:00
-- url     : https://prove2.me/theorems/437623c0-1b54-4e70-9e0c-d536c9f27e93
-- title:
--   FPP: fpp unit iff
-- statement:
--   The FPP construction uses the fpp unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L42-L46
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L42-L46

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP

theorem FPP.fpp_unit_iff {n : ℕ} {a : (ZMod n)ˣ} :
    FPP n a ↔ a ^ (n - 1) = 1 := by sorry
