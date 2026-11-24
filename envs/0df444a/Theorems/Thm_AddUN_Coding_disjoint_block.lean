-- Prove2me | Theorems.Thm_AddUN_Coding_disjoint_block
-- name    : AddUN.Coding.disjoint_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:22.973629+00:00
-- url     : https://prove2.me/theorems/12aea7a1-249a-4bec-87bd-b8f851a8270e
-- title:
--   Coding: disjoint block
-- statement:
--   The Coding construction uses the disjoint block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L101-L106
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L101-L106

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

theorem AddUN.Coding.disjoint_block {n k k' : ℕ} (h : k ≠ k') : Disjoint (block n k) (block n k') := by sorry
