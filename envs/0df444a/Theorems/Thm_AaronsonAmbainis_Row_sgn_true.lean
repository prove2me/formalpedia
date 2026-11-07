-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sgn_true
-- name    : AaronsonAmbainis.Row.sgn_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:55:27.425988+00:00
-- url     : https://prove2.me/theorems/ba8d47ea-fe3d-45ff-9457-abc2799ac36d
-- title:
--   Row: sgn true
-- statement:
--   The Row construction uses the sgn true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L22-L22
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L22-L22

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset

theorem AaronsonAmbainis.Row.sgn_true : sgn true = -1 := by sorry
