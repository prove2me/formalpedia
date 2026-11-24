-- Prove2me | Theorems.Thm_AddUN_Coding_hit_subset_marker
-- name    : AddUN.Coding.hit_subset_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:45.334239+00:00
-- url     : https://prove2.me/theorems/f28a6228-d1ba-47f2-ba1d-a58f5d12c048
-- title:
--   Coding: hit subset marker
-- statement:
--   The Coding construction uses the hit subset marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L135-L139
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L135-L139

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

theorem AddUN.Coding.hit_subset_marker (c : ℕ → Bool) (n k : ℕ) : hit c n k ⊆ marker n k := by sorry
