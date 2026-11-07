-- Prove2me | Theorems.Thm_AaronsonAmbainis_mem_diffSet
-- name    : AaronsonAmbainis.mem_diffSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:33.881894+00:00
-- url     : https://prove2.me/theorems/0d299055-2629-4848-9d9e-4b9faf256379
-- title:
--   Aaronson Ambainis: mem diff Set
-- statement:
--   The Aaronson Ambainis construction uses the mem diff Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L47-L48
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L47-L48

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.mem_diffSet {x y : Cube ι} {i : ι} : i ∈ diffSet x y ↔ x i ≠ y i := by sorry
