-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_fAg_flipSet_of_notMem
-- name    : AaronsonAmbainis.DetBij.fAg_flipSet_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:07.592588+00:00
-- url     : https://prove2.me/theorems/6d00d21a-c3aa-4021-8d20-559f6eb28308
-- title:
--   Det Bij: f Ag flip Set of not Mem
-- statement:
--   The Det Bij construction uses the f Ag flip Set of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L65-L68
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L65-L68

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetBij.fAg_flipSet_of_notMem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∉ S) :
    fAg (flipSet x S) z i = fAg x z i := by sorry
