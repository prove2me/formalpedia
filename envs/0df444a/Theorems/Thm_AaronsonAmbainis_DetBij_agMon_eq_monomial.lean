-- Prove2me | Theorems.Thm_AaronsonAmbainis_DetBij_agMon_eq_monomial
-- name    : AaronsonAmbainis.DetBij.agMon_eq_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:07.849204+00:00
-- url     : https://prove2.me/theorems/8c7d9f37-bf14-4a0f-9092-9dd69c613949
-- title:
--   Det Bij: ag Mon eq monomial
-- statement:
--   `agMon x z` is the monomial with exponent vector `agExp x z` and coefficient `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L96-L103
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean#L96-L103

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.DetBij.agMon_eq_monomial (x z : Cube ι) :
    agMon x z = monomial (agExp x z) (1 : ℤ) := by sorry
