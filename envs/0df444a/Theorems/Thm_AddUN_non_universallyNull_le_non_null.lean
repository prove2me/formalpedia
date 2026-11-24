-- Prove2me | Theorems.Thm_AddUN_non_universallyNull_le_non_null
-- name    : AddUN.non_universallyNull_le_non_null
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:24:05.15738+00:00
-- url     : https://prove2.me/theorems/fcce2df5-1b89-474d-ab73-70c4c47bd4c4
-- title:
--   Add UN: non universally Null le non null
-- statement:
--   The easy half of `GotoProp54`: `non 𝒰𝒩 ≤ non 𝒩`.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L115-L116
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L115-L116

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.non_universallyNull_le_non_null : non 𝒰𝒩 ≤ non 𝒩 := by sorry
