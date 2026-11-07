-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_flipSet
-- name    : AaronsonAmbainis.Bridge.flipSet_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:47:50.006022+00:00
-- url     : https://prove2.me/theorems/4712d35b-b1e9-455d-a9ea-898fe1991143
-- title:
--   Bridge: flip Set flip Set
-- statement:
--   The Bridge construction uses the flip Set flip Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L21-L23
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L21-L23

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.flipSet_flipSet (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by sorry
