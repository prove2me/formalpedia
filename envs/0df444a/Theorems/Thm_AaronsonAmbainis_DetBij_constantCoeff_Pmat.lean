-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_Pmat
-- name    : AaronsonAmbainis.DetBij.constantCoeff_Pmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:24.043943+00:00
-- url     : https://prove2.me/theorems/71e5288e-b2e3-465e-9593-bc9f88e27646
-- title:
--   Det Bij: constant Coeff Pmat
-- statement:
--   The Det Bij construction uses the constant Coeff Pmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L169-L183
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L169-L183

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.constantCoeff_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    constantCoeff (Pmat g A x w) = if x = w then 1 else 0 := by sorry
