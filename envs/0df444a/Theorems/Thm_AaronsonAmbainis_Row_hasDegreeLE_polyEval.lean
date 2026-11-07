-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_polyEval
-- name    : AaronsonAmbainis.Row.hasDegreeLE_polyEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:17.265653+00:00
-- url     : https://prove2.me/theorems/bac6dc26-e0c7-4d87-832c-8350b924abac
-- title:
--   Row: has Degree LE poly Eval
-- statement:
--   A real polynomial of a function of degree at most `1` has degree at most its `natDegree`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L133-L142
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L133-L142

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_polyEval (Q : Polynomial ℝ) {g : Cube β → ℝ} (hg : HasDegreeLE g 1) :
    HasDegreeLE (fun w => Q.eval (g w)) Q.natDegree := by sorry
