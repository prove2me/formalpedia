-- Prove2me | Theorems.Thm_AddUN_Coding_isClopen_marker
-- name    : AddUN.Coding.isClopen_marker
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:25:03.049154+00:00
-- url     : https://prove2.me/theorems/f9f8d6a0-69d9-4c97-86e7-4e112c4b4e81
-- title:
--   Coding: is Clopen marker
-- statement:
--   The Coding construction uses the is Clopen marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L145-L145
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L145-L145

module
public import Definitions.Def_AddUN_SecondMoment
public import Definitions.Def_AddUN_TheoremB
public import Definitions.Def_AddUN_Coding
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory
open AddUN
open AddUN.Coding

theorem AddUN.Coding.isClopen_marker (n k : ℕ) : IsClopen (marker n k) := by sorry
