-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_gadget_zero
-- name    : AaronsonAmbainis.Row.gadget_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:05:44.499734+00:00
-- url     : https://prove2.me/theorems/934e13e4-9144-4206-a037-4e90e17783b1
-- title:
--   Row: gadget zero
-- statement:
--   The Row construction uses the gadget zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L140-L147
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L140-L147

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.gadget_zero (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    gadget a x S m c (zero β) = ∑ T, a T * chi T x := by sorry
