-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_gate_zero
-- name    : AaronsonAmbainis.Row.gate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:41.959941+00:00
-- url     : https://prove2.me/theorems/79788370-b3c6-4a41-b348-c6dcf43b4d20
-- title:
--   Row: gate zero
-- statement:
--   The Row construction uses the gate zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L100-L102
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L100-L102

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]

theorem AaronsonAmbainis.Row.gate_zero (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) : gate S m c i (zero β) = 1 := by sorry
