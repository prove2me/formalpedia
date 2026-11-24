-- Prove2me | Theorems.Thm_AddUN_Coding_markerBlock_subset_block
-- name    : AddUN.Coding.markerBlock_subset_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:20.459751+00:00
-- url     : https://prove2.me/theorems/a25ed13c-1918-4a65-9735-86d41a506483
-- title:
--   Coding: marker Block subset block
-- statement:
--   The Coding construction uses the marker Block subset block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L92-L93
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L92-L93

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

theorem AddUN.Coding.markerBlock_subset_block (n k : ℕ) : markerBlock n k ⊆ block n k := by sorry
