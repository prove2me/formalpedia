-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_cofactor_le
-- name    : AaronsonAmbainis.DetLow.degreeOf_cofactor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:55:56.239493+00:00
-- url     : https://prove2.me/theorems/6fac3114-8b1a-4d2b-a327-ed9e70a58836
-- title:
--   Det Low: degree Of cofactor le
-- statement:
--   The cofactor `R` of `(1 - s_j^2)^(e_j)` has degree at most `b_j(g)` in `s_j` (proof of
--   Lemma 3.6 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L26-L46
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Main.lean#L26-L46

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

theorem AaronsonAmbainis.DetLow.degreeOf_cofactor_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (j : ι)
    (R : MvPolynomial ι ℤ) (hR : (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R) :
    degreeOf j R ≤ bdry g j := by sorry
