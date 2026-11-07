-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_antipode_eq_flipSet_univ
-- name    : AaronsonAmbainis.Bridge.antipode_eq_flipSet_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:08.494881+00:00
-- url     : https://prove2.me/theorems/54809b4e-af70-4859-a7ec-d3eea7e6e3a1
-- title:
--   Bridge: antipode eq flip Set univ
-- statement:
--   `antipode x = x^{[n]}`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L76-L78
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Basic.lean#L76-L78

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by sorry
