-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_det_Umat
-- name    : AaronsonAmbainis.DetBij.constantCoeff_det_Umat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:32.539988+00:00
-- url     : https://prove2.me/theorems/694950b8-e135-4a6d-aa0f-8f46368e879c
-- title:
--   Det Bij: constant Coeff det Umat
-- statement:
--   The Det Bij construction uses the constant Coeff det Umat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L193-L200
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L193-L200

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.constantCoeff_det_Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Umat g A).det = 1 := by sorry
