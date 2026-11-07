-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_flipSet_antipode_agSet
-- name    : AaronsonAmbainis.DetBij.flipSet_antipode_agSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:01.09143+00:00
-- url     : https://prove2.me/theorems/706ddc3a-9ca8-4ec2-be82-3bfd8be392a3
-- title:
--   Det Bij: flip Set antipode ag Set
-- statement:
--   `z` is the antipode of `u` flipped on the agreement set of `u` and `z`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L68-L77
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L68-L77

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.flipSet_antipode_agSet (u z : Cube ι) : flipSet (antipode u) (agSet u z) = z := by sorry
