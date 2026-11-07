-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_gate_unit
-- name    : AaronsonAmbainis.Row.gate_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:05:32.242751+00:00
-- url     : https://prove2.me/theorems/8afb3452-3e19-4200-a7e8-21aa9ade65cc
-- title:
--   Row: gate unit
-- statement:
--   The Row construction uses the gate unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L105-L115
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L105-L115

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]

theorem AaronsonAmbainis.Row.gate_unit [DecidableEq β] (S : β → Finset ι) (m : ℕ) (hm : 0 < m) (i : ι) (b : β) :
    gate S m (1 - Real.cos (Real.pi / (m : ℝ))) i (unit b) = if i ∈ S b then -1 else 1 := by sorry
