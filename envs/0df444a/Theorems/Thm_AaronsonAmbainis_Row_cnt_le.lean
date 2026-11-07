-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_cnt_le
-- name    : AaronsonAmbainis.Row.cnt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:32.449338+00:00
-- url     : https://prove2.me/theorems/40435aa4-65b1-4926-96e3-1a2ffd5cb58c
-- title:
--   Row: cnt le
-- statement:
--   The Row construction uses the cnt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L46-L55
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean#L46-L55

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_Row_Gadget
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
omit [Fintype ι]

theorem AaronsonAmbainis.Row.cnt_le (S : β → Finset ι) (N : ℕ)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (i : ι) (w : Cube β) :
    cnt S i w ≤ N := by sorry
