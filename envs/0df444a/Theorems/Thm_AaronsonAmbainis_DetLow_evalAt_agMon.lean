-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_evalAt_agMon
-- name    : AaronsonAmbainis.DetLow.evalAt_agMon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:22.474849+00:00
-- url     : https://prove2.me/theorems/e675aa25-4da1-42bd-b91d-c34e7eec5449
-- title:
--   Det Low: eval At ag Mon
-- statement:
--   The Det Low construction uses the eval At ag Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L28-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L28-L40

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.evalAt_agMon (c : ℝ) (x z : Cube ι) :
    evalAt c (agMon x z) = c ^ agCount x z := by sorry
