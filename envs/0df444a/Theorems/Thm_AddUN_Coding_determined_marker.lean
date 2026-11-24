-- Prove2me | Theorems.Thm_AddUN_Coding_determined_marker
-- name    : AddUN.Coding.determined_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:49.575736+00:00
-- url     : https://prove2.me/theorems/de427593-bef0-4869-baef-02b7b2cb5994
-- title:
--   Coding: determined marker
-- statement:
--   The Coding construction uses the determined marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L149-L151
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L149-L151

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

theorem AddUN.Coding.determined_marker (n k : ℕ) : Determined (low (n + 1)) (marker n k) := by sorry
