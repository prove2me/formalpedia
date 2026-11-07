-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_prod
-- name    : AaronsonAmbainis.Row.hasDegreeLE_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:21.368636+00:00
-- url     : https://prove2.me/theorems/90353df2-a648-461b-8914-060385f77749
-- title:
--   Row: has Degree LE prod
-- statement:
--   The Row construction uses the has Degree LE prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L117-L130
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Degree.lean#L117-L130

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]

theorem AaronsonAmbainis.Row.hasDegreeLE_prod {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) :
    HasDegreeLE (fun w => ∏ j ∈ s, F j w) (s.card * k) := by sorry
