-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_cnt_unit
-- name    : AaronsonAmbainis.Row.cnt_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:32.978063+00:00
-- url     : https://prove2.me/theorems/c1a9551a-65d8-4a86-958b-1b2cc4b07a17
-- title:
--   Row: cnt unit
-- statement:
--   The Row construction uses the cnt unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L62-L64
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L62-L64

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]

theorem AaronsonAmbainis.Row.cnt_unit [DecidableEq β] (S : β → Finset ι) (i : ι) (b : β) :
    cnt S i (unit b) = if i ∈ S b then 1 else 0 := by sorry
