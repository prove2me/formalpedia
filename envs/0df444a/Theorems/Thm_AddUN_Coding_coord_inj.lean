-- Prove2me | Theorems.Thm_AddUN_Coding_coord_inj
-- name    : AddUN.Coding.coord_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:23:48.278616+00:00
-- url     : https://prove2.me/theorems/1335f061-856b-4d43-92b6-60c183d63184
-- title:
--   Coding: coord inj
-- statement:
--   The Coding construction uses the coord inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L65-L67
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Coding.lean#L65-L67

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

theorem AddUN.Coding.coord_inj {n k j n' k' j' : ℕ} :
    coord n k j = coord n' k' j' ↔ n = n' ∧ k = k' ∧ j = j' := by sorry
