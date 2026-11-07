-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_card_ones_eq
-- name    : AaronsonAmbainis.DetLow.card_ones_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:54:23.763497+00:00
-- url     : https://prove2.me/theorems/6ac3b922-2603-497f-bd7b-5076088cf2ff
-- title:
--   Det Low: card ones eq
-- statement:
--   The number of ones of `g` is `2 e_j + b_j(g)` (proof of Lemma 3.6 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L66-L91
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Count.lean#L66-L91

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_Count
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.card_ones_eq (g : Cube ι → Bool) (j : ι) :
    Fintype.card (Ones g) = 2 * (Up g j).card + bdry g j := by sorry
