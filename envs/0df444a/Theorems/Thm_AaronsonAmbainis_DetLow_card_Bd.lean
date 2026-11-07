-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_card_Bd
-- name    : AaronsonAmbainis.DetLow.card_Bd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:17.08184+00:00
-- url     : https://prove2.me/theorems/4d3b024c-e180-4842-b967-9d80d25c4792
-- title:
--   Det Low: card Bd
-- statement:
--   The Det Low construction uses the card Bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L53-L63
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L53-L63

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.card_Bd (g : Cube ι → Bool) (j : ι) : (Bd g j).card = bdry g j := by sorry
