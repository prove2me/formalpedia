-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_prod_erase_flipSet
-- name    : AaronsonAmbainis.DetLow.prod_erase_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:27:20.904844+00:00
-- url     : https://prove2.me/theorems/f79793a1-2076-4fe1-aa4c-4f35442d4b1e
-- title:
--   Det Low: prod erase flip Set
-- statement:
--   The Det Low construction uses the prod erase flip Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L27-L32
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/RowOps.lean#L27-L32

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.prod_erase_flipSet (x z : Cube ι) (j : ι) :
    ∏ i ∈ univ.erase j, (if flipSet x {j} i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by sorry
