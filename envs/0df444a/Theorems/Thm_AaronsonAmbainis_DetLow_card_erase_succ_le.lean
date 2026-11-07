-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_card_erase_succ_le
-- name    : AaronsonAmbainis.DetLow.card_erase_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:43.698038+00:00
-- url     : https://prove2.me/theorems/c7629605-a47e-4b54-89fd-14f1febb5048
-- title:
--   Det Low: card erase succ le
-- statement:
--   A row of the ones of `g` has fewer than `2 ^ n` off-diagonal entries.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L60-L68
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L60-L68

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.card_erase_succ_le (g : Cube ι → Bool) (x : Ones g) :
    (univ.erase x).card + 1 ≤ 2 ^ Fintype.card ι := by sorry
