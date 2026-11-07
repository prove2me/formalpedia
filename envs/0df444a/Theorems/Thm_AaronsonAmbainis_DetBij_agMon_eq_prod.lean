-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_agMon_eq_prod
-- name    : AaronsonAmbainis.DetBij.agMon_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:58.787725+00:00
-- url     : https://prove2.me/theorems/ec584ef4-bab5-4643-b7bc-c71baadc96de
-- title:
--   Det Bij: ag Mon eq prod
-- statement:
--   The Det Bij construction uses the ag Mon eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L55-L55
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean#L55-L55

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.agMon_eq_prod (x z : Cube ι) : agMon x z = ∏ i, fAg x z i := by sorry
