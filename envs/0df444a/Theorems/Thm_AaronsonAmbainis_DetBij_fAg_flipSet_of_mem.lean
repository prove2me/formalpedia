-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_fAg_flipSet_of_mem
-- name    : AaronsonAmbainis.DetBij.fAg_flipSet_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:03.229518+00:00
-- url     : https://prove2.me/theorems/58f15424-1332-4e77-abca-73e8e156815a
-- title:
--   Det Bij: f Ag flip Set of mem
-- statement:
--   The Det Bij construction uses the f Ag flip Set of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L58-L62
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L58-L62

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetBij.fAg_flipSet_of_mem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∈ S) :
    fAg (flipSet x S) z i = gAg x z i := by sorry
