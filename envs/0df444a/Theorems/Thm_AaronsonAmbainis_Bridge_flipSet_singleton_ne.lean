-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_ne
-- name    : AaronsonAmbainis.Bridge.flipSet_singleton_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:44.653494+00:00
-- url     : https://prove2.me/theorems/e772fdbc-655a-4ec2-b538-aca8e08a51be
-- title:
--   Bridge: flip Set singleton ne
-- statement:
--   The Bridge construction uses the flip Set singleton ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L32-L33
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L32-L33

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.flipSet_singleton_ne (x : Cube ι) {i j : ι} (h : i ≠ j) : flipSet x {j} i = x i := by sorry
