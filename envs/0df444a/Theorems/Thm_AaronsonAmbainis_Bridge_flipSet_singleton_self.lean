-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_self
-- name    : AaronsonAmbainis.Bridge.flipSet_singleton_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:06.267332+00:00
-- url     : https://prove2.me/theorems/05cb914d-d700-4f92-9afc-53fc26b2a582
-- title:
--   Bridge: flip Set singleton self
-- statement:
--   The Bridge construction uses the flip Set singleton self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L29-L30
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L29-L30

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.flipSet_singleton_self (x : Cube ι) (j : ι) : flipSet x {j} j = !(x j) := by sorry
