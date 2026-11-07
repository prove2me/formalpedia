-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_unit_mul
-- name    : AaronsonAmbainis.DetLow.isLowest_unit_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:44.512559+00:00
-- url     : https://prove2.me/theorems/6768e012-6c11-4289-a545-235787ad27d0
-- title:
--   Det Low: is Lowest unit mul
-- statement:
--   Forward direction of `LowestUnit`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L52-L69
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L52-L69

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.isLowest_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest q m) : IsLowest (u * q) m := by sorry
