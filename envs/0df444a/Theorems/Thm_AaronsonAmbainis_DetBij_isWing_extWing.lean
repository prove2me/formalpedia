-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_isWing_extWing
-- name    : AaronsonAmbainis.DetBij.isWing_extWing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:04.27506+00:00
-- url     : https://prove2.me/theorems/7bed0409-0816-43d3-af32-83a2c7fea007
-- title:
--   Det Bij: is Wing ext Wing
-- statement:
--   The extended wings are 1-wings at every one of `g` (the empty set is a 1-wing).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L32-L41
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L32-L41

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.isWing_extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ u ∈ zone g, IsWing g u (A u)) (x : Ones g) :
    IsWing g x.1 (extWing g A x.1) := by sorry
