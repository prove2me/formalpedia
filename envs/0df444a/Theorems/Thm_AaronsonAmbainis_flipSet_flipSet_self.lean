-- Prove2me | Theorems.Thm_AaronsonAmbainis_flipSet_flipSet_self
-- name    : AaronsonAmbainis.flipSet_flipSet_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:05.384244+00:00
-- url     : https://prove2.me/theorems/23280b14-51ce-46da-86cc-b90eae5a4e5a
-- title:
--   Aaronson Ambainis: flip Set flip Set self
-- statement:
--   The Aaronson Ambainis construction uses the flip Set flip Set self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L22-L24
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L22-L24

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.flipSet_flipSet_self (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by sorry
