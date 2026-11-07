-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_card_Dn
-- name    : AaronsonAmbainis.DetLow.card_Dn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:05.623741+00:00
-- url     : https://prove2.me/theorems/57177fbb-558f-4fda-8101-7c55a1aa3c0d
-- title:
--   Det Low: card Dn
-- statement:
--   The Det Low construction uses the card Dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L35-L51
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L35-L51

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.card_Dn (g : Cube ι → Bool) (j : ι) : (Dn g j).card = (Up g j).card := by sorry
