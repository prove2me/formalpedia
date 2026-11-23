-- Prove2me | Theorems.Thm_FPP_isUnit
-- name    : FPP.isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:00:36.227501+00:00
-- url     : https://prove2.me/theorems/31e5f481-6a29-4dc6-8d2e-aff950bc9f27
-- title:
--   FPP: is Unit
-- statement:
--   The FPP construction uses the is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L38-L40
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/FermatProbable.lean#L38-L40

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable
set_option autoImplicit false
open Nat
open FPP

theorem FPP.isUnit {n : ℕ} [hn : Fact (1 < n)] {a : ZMod n} (h : FPP n a) :
    IsUnit a := by sorry
