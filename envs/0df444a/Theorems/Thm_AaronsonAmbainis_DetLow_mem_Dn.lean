-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_mem_Dn
-- name    : AaronsonAmbainis.DetLow.mem_Dn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:53:58.730385+00:00
-- url     : https://prove2.me/theorems/141053fd-4029-4d57-a179-def0322f31d5
-- title:
--   Det Low: mem Dn
-- statement:
--   The Det Low construction uses the mem Dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L27-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L27-L29

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.mem_Dn {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Dn g j ↔ x.1 j = false ∧ g (flipSet x.1 {j}) = true := by sorry
