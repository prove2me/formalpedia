-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_det_Pmat
-- name    : AaronsonAmbainis.DetBij.constantCoeff_det_Pmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:24.141198+00:00
-- url     : https://prove2.me/theorems/5d0fc7d2-1867-4cb9-9783-f7da6d8bdb8d
-- title:
--   Det Bij: constant Coeff det Pmat
-- statement:
--   The Det Bij construction uses the constant Coeff det Pmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L185-L191
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L185-L191

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.constantCoeff_det_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Pmat g A).det = 1 := by sorry
