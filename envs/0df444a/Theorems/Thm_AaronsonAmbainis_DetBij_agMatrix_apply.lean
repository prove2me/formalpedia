-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_agMatrix_apply
-- name    : AaronsonAmbainis.DetBij.agMatrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:50.576821+00:00
-- url     : https://prove2.me/theorems/31366aae-9419-4bb2-a60d-666e1e2304b2
-- title:
--   Det Bij: ag Matrix apply
-- statement:
--   The Det Bij construction uses the ag Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L43-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L43-L44

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := by sorry
