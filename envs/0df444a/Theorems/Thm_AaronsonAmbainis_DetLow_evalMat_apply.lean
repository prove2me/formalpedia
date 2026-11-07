-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_evalMat_apply
-- name    : AaronsonAmbainis.DetLow.evalMat_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:37.816334+00:00
-- url     : https://prove2.me/theorems/074cbfa3-5daf-4c3e-a608-ea23d4ca34da
-- title:
--   Det Low: eval Mat apply
-- statement:
--   The Det Low construction uses the eval Mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L55-L57
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L55-L57

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.evalMat_apply (c : ℝ) (g : Cube ι → Bool) (x z : Ones g) :
    (evalAt c).mapMatrix (agMatrix g) x z = c ^ agCount x.1 z.1 := by sorry
