-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_evalMat_dominant
-- name    : AaronsonAmbainis.DetLow.evalMat_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:14.387022+00:00
-- url     : https://prove2.me/theorems/8f9b730c-879a-4a29-a211-a4202ed3708e
-- title:
--   Det Low: eval Mat dominant
-- statement:
--   The evaluated matrix is strictly diagonally dominant when `c = 2 ^ n`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L71-L106
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean#L71-L106

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.DetLow.evalMat_dominant (g : Cube ι → Bool) (c : ℝ) (hc : c = 2 ^ Fintype.card ι)
    (x : Ones g) :
    ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖
      < ‖(evalAt c).mapMatrix (agMatrix g) x x‖ := by sorry
