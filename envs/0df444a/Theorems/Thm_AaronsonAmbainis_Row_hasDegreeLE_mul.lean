-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_mul
-- name    : AaronsonAmbainis.Row.hasDegreeLE_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:00:10.120073+00:00
-- url     : https://prove2.me/theorems/747efaa2-3fca-4140-839c-d6e208c99262
-- title:
--   Row: has Degree LE mul
-- statement:
--   Products add degrees.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L74-L105
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L74-L105

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_mul {f g : Cube β → ℝ} {k l : ℕ} (hf : HasDegreeLE f k)
    (hg : HasDegreeLE g l) : HasDegreeLE (fun w => f w * g w) (k + l) := by sorry
