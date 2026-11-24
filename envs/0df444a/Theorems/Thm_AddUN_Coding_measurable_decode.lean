-- Prove2me | Theorems.Thm_AddUN_Coding_measurable_decode
-- name    : AddUN.Coding.measurable_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:30:58.00132+00:00
-- url     : https://prove2.me/theorems/7d3ca36f-0182-413a-ab77-8805d8870c9b
-- title:
--   Coding: measurable decode
-- statement:
--   The Coding construction uses the measurable decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L167-L183
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L167-L183

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

theorem AddUN.Coding.measurable_decode (f : ℕ → ℕ) : Measurable (decode f) := by sorry
