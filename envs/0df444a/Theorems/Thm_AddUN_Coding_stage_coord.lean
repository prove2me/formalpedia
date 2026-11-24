-- Prove2me | Theorems.Thm_AddUN_Coding_stage_coord
-- name    : AddUN.Coding.stage_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:51.778173+00:00
-- url     : https://prove2.me/theorems/36e65ac1-ade3-4e7d-95f8-f9e4d6de6f3b
-- title:
--   Coding: stage coord
-- statement:
--   The Coding construction uses the stage coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L63-L63
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L63-L63

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

theorem AddUN.Coding.stage_coord (n k j : ℕ) : stage (coord n k j) = n := by sorry
