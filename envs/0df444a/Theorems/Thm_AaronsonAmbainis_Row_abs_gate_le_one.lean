-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_abs_gate_le_one
-- name    : AaronsonAmbainis.Row.abs_gate_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:47.607093+00:00
-- url     : https://prove2.me/theorems/305321de-c64c-4bbb-a296-0e45a694848a
-- title:
--   Row: abs gate le one
-- statement:
--   The Row construction uses the abs gate le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L74-L82
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L74-L82

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]

theorem AaronsonAmbainis.Row.abs_gate_le_one (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (i : ι) (w : Cube β) : |gate S m c i w| ≤ 1 := by sorry
