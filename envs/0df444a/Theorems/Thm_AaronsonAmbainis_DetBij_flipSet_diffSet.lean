-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_diffSet
-- name    : AaronsonAmbainis.DetBij.flipSet_diffSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:10.552661+00:00
-- url     : https://prove2.me/theorems/fb8e2f32-b1c9-4c92-a89b-853a95e6bb3c
-- title:
--   Det Bij: flip Set diff Set
-- statement:
--   A point `w` with `diffSet x w = S` is `flipSet x S`: second half.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L43-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L43-L52

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.flipSet_diffSet (x w : Cube ι) : flipSet x (diffSet x w) = w := by sorry
