-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_diffSet_flipSet
-- name    : AaronsonAmbainis.DetBij.diffSet_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:40.65785+00:00
-- url     : https://prove2.me/theorems/61f17502-921e-4953-94c4-df65a2f0229e
-- title:
--   Det Bij: diff Set flip Set
-- statement:
--   A point `w` with `diffSet x w = S` is `flipSet x S`: first half.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L37-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L37-L40

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by sorry
