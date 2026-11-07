-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sgn_not
-- name    : AaronsonAmbainis.Row.sgn_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:20.224127+00:00
-- url     : https://prove2.me/theorems/5e2a5dec-0471-4221-9dad-a60c6db75b64
-- title:
--   Row: sgn not
-- statement:
--   The Row construction uses the sgn not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L30-L30
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Chi.lean#L30-L30

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Chi
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset

theorem AaronsonAmbainis.Row.sgn_not (b : Bool) : sgn (!b) = -sgn b := by sorry
