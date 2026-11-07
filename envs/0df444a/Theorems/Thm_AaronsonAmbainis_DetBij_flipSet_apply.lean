-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_apply
-- name    : AaronsonAmbainis.DetBij.flipSet_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:57.004979+00:00
-- url     : https://prove2.me/theorems/3d15559b-47eb-47ea-b43a-c9dab4f995e9
-- title:
--   Det Bij: flip Set apply
-- statement:
--   The Det Bij construction uses the flip Set apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L28-L29
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L28-L29

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.DetBij.flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := by sorry
