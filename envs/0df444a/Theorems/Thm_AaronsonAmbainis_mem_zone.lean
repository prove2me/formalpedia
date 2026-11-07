-- Prove2me | Theorems.Thm_AaronsonAmbainis_mem_zone
-- name    : AaronsonAmbainis.mem_zone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:30.044751+00:00
-- url     : https://prove2.me/theorems/013d9d57-45ae-4b57-b9bb-a3023cb003cb
-- title:
--   Aaronson Ambainis: mem zone
-- statement:
--   The Aaronson Ambainis construction uses the mem zone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L50-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Basic.lean#L50-L52

import Definitions.Def_AaronsonAmbainis_AllPairsDefs
import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.mem_zone {g : Cube ι → Bool} {u : Cube ι} :
    u ∈ zone g ↔ g u = true ∧ g (antipode u) = false := by sorry
