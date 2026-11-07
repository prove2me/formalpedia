-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_eq_zero_of_degree_zero
-- name    : AaronsonAmbainis.Bridge.variance_eq_zero_of_degree_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:19.715094+00:00
-- url     : https://prove2.me/theorems/556c7850-4fb6-408e-a060-3947b90997b3
-- title:
--   Bridge: variance eq zero of degree zero
-- statement:
--   Degree `0` forces variance `0`: the `d = 0` instance of `MainTheorem` is vacuous.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L48-L50
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L48-L50

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.variance_eq_zero_of_degree_zero {f : Cube ι → ℝ} (h : HasDegreeLE f 0) :
    variance f = 0 := by sorry
