-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_one_le_card_of_ne
-- name    : AaronsonAmbainis.Bridge.one_le_card_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:02.087352+00:00
-- url     : https://prove2.me/theorems/01a683dc-035b-469e-8d02-888ec0d2b82b
-- title:
--   Bridge: one le card of ne
-- statement:
--   The Bridge construction uses the one le card of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L169-L172
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Positivity.lean#L169-L172

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.one_le_card_of_ne {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) :
    1 ≤ Fintype.card ι := by sorry
