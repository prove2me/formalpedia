-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_gadget_unit
-- name    : AaronsonAmbainis.Row.gadget_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:05:50.184409+00:00
-- url     : https://prove2.me/theorems/5741d52c-2d10-4f3d-bafb-18f093532081
-- title:
--   Row: gadget unit
-- statement:
--   The Row construction uses the gadget unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L149-L158
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L149-L158

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.gadget_unit [DecidableEq β] (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ)
    (hm : 0 < m) (b : β) :
    gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (unit b)
      = ∑ T, a T * chi T (flipSet x (S b)) := by sorry
