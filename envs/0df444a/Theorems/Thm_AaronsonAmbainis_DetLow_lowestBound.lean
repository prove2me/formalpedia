-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_lowestBound
-- name    : AaronsonAmbainis.DetLow.lowestBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:04.291201+00:00
-- url     : https://prove2.me/theorems/3bcf68f5-0db3-47be-a5cf-f162c4dda9ef
-- title:
--   Det Low: lowest Bound
-- statement:
--   Lemma 3.4 and Lemma 3.6 of the paper: the determinant of the agreement matrix is nonzero, and
--   each of its monomials of least total degree has exponent at most `b_j(g)` in every variable
--   `s_j`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L51-L60
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L51-L60

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

theorem AaronsonAmbainis.DetLow.lowestBound : AaronsonAmbainis.LowestBound := by sorry
