-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_lowestUnit
-- name    : AaronsonAmbainis.DetLow.lowestUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:03.084654+00:00
-- url     : https://prove2.me/theorems/23f785ee-8d71-4c5e-85c5-914830dc68c3
-- title:
--   Det Low: lowest Unit
-- statement:
--   Lemma 3.3 of the paper: multiplying by a polynomial with constant coefficient `1` does not
--   change the monomials of least total degree.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L20-L22
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L20-L22

import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Definitions.Def_AaronsonAmbainis_DetLow_Main
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.lowestUnit : AaronsonAmbainis.LowestUnit := by sorry
