-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_sum
-- name    : AaronsonAmbainis.Row.hasDegreeLE_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:00:24.056724+00:00
-- url     : https://prove2.me/theorems/b404e8d0-f892-4c9c-ace8-5643cc168646
-- title:
--   Row: has Degree LE sum
-- statement:
--   The Row construction uses the has Degree LE sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L58-L66
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L58-L66

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_sum {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) : HasDegreeLE (fun w => ∑ j ∈ s, F j w) k := by sorry
