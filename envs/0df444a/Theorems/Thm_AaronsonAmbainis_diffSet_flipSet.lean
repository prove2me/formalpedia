-- Prove2me | Theorems.Thm_AaronsonAmbainis_diffSet_flipSet
-- name    : AaronsonAmbainis.diffSet_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:25.258191+00:00
-- url     : https://prove2.me/theorems/fcaa6d04-4309-44eb-9eaa-cd41fbe865ed
-- title:
--   Aaronson Ambainis: diff Set flip Set
-- statement:
--   The Aaronson Ambainis construction uses the diff Set flip Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L34-L36
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L34-L36

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by sorry
