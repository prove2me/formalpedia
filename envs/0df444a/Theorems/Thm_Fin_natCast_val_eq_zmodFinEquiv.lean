-- Prove2me | Theorems.Thm_Fin_natCast_val_eq_zmodFinEquiv
-- name    : Fin.natCast_val_eq_zmodFinEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:52:57.612062+00:00
-- url     : https://prove2.me/theorems/9a7cbb8d-d850-4cb6-a2db-dc1b6a425d2e
-- title:
--   Fin: nat Cast val eq zmod Fin Equiv
-- statement:
--   The Fin construction uses the nat Cast val eq zmod Fin Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Mathlib/Data/ZMod/Basic.lean#L7-L14
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/Mathlib/Data/ZMod/Basic.lean#L7-L14

module
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
set_option autoImplicit true
@[expose] public section
public section

theorem Fin.natCast_val_eq_zmodFinEquiv {n : ℕ} [NeZero n] (a : Fin n) :
    a = ZMod.finEquiv n a := by sorry
