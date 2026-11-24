-- Prove2me | Theorems.Thm_AddUN_Coding_low_mono
-- name    : AddUN.Coding.low_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:30.402227+00:00
-- url     : https://prove2.me/theorems/82952506-d0d0-40e8-a4ef-f6357efe126a
-- title:
--   Coding: low mono
-- statement:
--   The Coding construction uses the low mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L72-L72
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L72-L72

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

theorem AddUN.Coding.low_mono {m n : ℕ} (h : m ≤ n) : low m ⊆ low n := by sorry
