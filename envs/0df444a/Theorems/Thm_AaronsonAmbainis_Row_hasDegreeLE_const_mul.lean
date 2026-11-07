-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const_mul
-- name    : AaronsonAmbainis.Row.hasDegreeLE_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:40.668191+00:00
-- url     : https://prove2.me/theorems/d30daaef-86ea-4325-a2eb-431aac6df537
-- title:
--   Row: has Degree LE const mul
-- statement:
--   The Row construction uses the has Degree LE const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L46-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L46-L52

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_const_mul (a : ℝ) {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) :
    HasDegreeLE (fun w => a * f w) k := by sorry
