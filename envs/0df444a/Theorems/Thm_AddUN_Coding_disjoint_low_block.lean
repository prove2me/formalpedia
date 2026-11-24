-- Prove2me | Theorems.Thm_AddUN_Coding_disjoint_low_block
-- name    : AddUN.Coding.disjoint_low_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:19.942498+00:00
-- url     : https://prove2.me/theorems/5cd0951c-613b-4e45-aa53-ddf033eff87e
-- title:
--   Coding: disjoint low block
-- statement:
--   The Coding construction uses the disjoint low block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L95-L99
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L95-L99

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

theorem AddUN.Coding.disjoint_low_block (n k : ℕ) : Disjoint (low n) (block n k : Set ℕ) := by sorry
