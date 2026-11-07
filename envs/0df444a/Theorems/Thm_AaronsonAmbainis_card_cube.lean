-- Prove2me | Theorems.Thm_AaronsonAmbainis_card_cube
-- name    : AaronsonAmbainis.card_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:19.272065+00:00
-- url     : https://prove2.me/theorems/f8f50e05-eb0b-41a7-82fe-eee8134a63c4
-- title:
--   Aaronson Ambainis: card cube
-- statement:
--   The Aaronson Ambainis construction uses the card cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L54-L55
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L54-L55

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.card_cube : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by sorry
