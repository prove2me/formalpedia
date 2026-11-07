-- Prove2me | Theorems.Thm_AaronsonAmbainis_flipSet_apply
-- name    : AaronsonAmbainis.flipSet_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:01.329503+00:00
-- url     : https://prove2.me/theorems/f6f248a2-c675-45e8-bc31-dbb20f5fb6e0
-- title:
--   Aaronson Ambainis: flip Set apply
-- statement:
--   The Aaronson Ambainis construction uses the flip Set apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L15-L16
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L15-L16

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := by sorry
