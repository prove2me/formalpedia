-- Prove2me | Theorems.Thm_AaronsonAmbainis_flipSet_empty
-- name    : AaronsonAmbainis.flipSet_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:19.492168+00:00
-- url     : https://prove2.me/theorems/df088c49-0c11-48aa-bb6f-4dbde99c6cb5
-- title:
--   Aaronson Ambainis: flip Set empty
-- statement:
--   The Aaronson Ambainis construction uses the flip Set empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L18-L20
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L18-L20

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by sorry
