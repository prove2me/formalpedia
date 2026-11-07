-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetLow_isLowest_of_unit_mul
-- name    : AaronsonAmbainis.DetLow.isLowest_of_unit_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:19:54.837835+00:00
-- url     : https://prove2.me/theorems/8ae125e9-003d-4863-8dfd-3b78b98a73b6
-- title:
--   Det Low: is Lowest of unit mul
-- statement:
--   Backward direction of `LowestUnit`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L82-L96
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/Unit.lean#L82-L96

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetLow_Unit
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial

theorem AaronsonAmbainis.DetLow.isLowest_of_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest (u * q) m) : IsLowest q m := by sorry
