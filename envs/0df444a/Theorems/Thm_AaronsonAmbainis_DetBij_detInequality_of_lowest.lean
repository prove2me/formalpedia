-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_detInequality_of_lowest
-- name    : AaronsonAmbainis.DetBij.detInequality_of_lowest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:32:20.624213+00:00
-- url     : https://prove2.me/theorems/95e75434-5f3c-4695-8979-0d4a18434226
-- title:
--   Det Bij: det Inequality of lowest
-- statement:
--   The determinant inequality (Corollary 3.2 of the paper) from `LowestUnit` and
--   `LowestBound`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L110-L116
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Main.lean#L110-L116

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.detInequality_of_lowest :
    AaronsonAmbainis.LowestUnit → AaronsonAmbainis.LowestBound → AaronsonAmbainis.DetInequality := by sorry
