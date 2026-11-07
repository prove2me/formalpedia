-- Prove2me | Theorems.Thm_AaronsonAmbainis_antipodal_of_det
-- name    : AaronsonAmbainis.antipodal_of_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:08.270579+00:00
-- url     : https://prove2.me/theorems/178bc7a8-b4a6-4788-84bc-45d732d9dd53
-- title:
--   Aaronson Ambainis: antipodal of det
-- statement:
--   The antipodal inequality (the inequality of Theorem 4.3 of the paper) from the determinant
--   inequality (Corollary 3.2).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L116-L129
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L116-L129

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.antipodal_of_det : DetInequality → AntipodalInequality := by sorry
