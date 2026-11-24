-- Prove2me | Theorems.Thm_AddUN_universallyNull_subset_null
-- name    : AddUN.universallyNull_subset_null
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T07:23:19.99469+00:00
-- url     : https://prove2.me/theorems/84d08643-d49f-416e-812f-ea38c9e8af61
-- title:
--   Add UN: universally Null subset null
-- statement:
--   Every universally null set is null.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L94-L95
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Statements.lean#L94-L95

module
public import Definitions.Def_AddUN_UniversallyNull
public import Definitions.Def_AddUN_Statements
set_option autoImplicit false
@[expose] public section
public section
open Cardinal MeasureTheory IdealInvariant Filter
open AddUN

theorem AddUN.universallyNull_subset_null : 𝒰𝒩 ⊆ 𝒩 := by sorry
