-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_exists_isLowest
-- name    : AaronsonAmbainis.DetLow.exists_isLowest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:18.565551+00:00
-- url     : https://prove2.me/theorems/03e67dbe-d720-4c58-85b8-b90da82a875d
-- title:
--   Det Low: exists is Lowest
-- statement:
--   A nonzero polynomial has a monomial of least total degree.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L72-L79
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L72-L79

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.exists_isLowest {ι : Type} [Fintype ι] (q : MvPolynomial ι ℤ) (hq : q ≠ 0) :
    ∃ m, IsLowest q m := by sorry
